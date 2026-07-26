Review status: awaiting human approval

# M8c Bieberbach bridge design review

This document fixes the proposed design for the converse geometric bridge.  It is an API and
proof-route review only: no M8c production theorem is implemented here.

The audit used the current project sources and the mathlib revision pinned by this repository.
Names listed as existing declarations were confirmed by source search and small compilation
experiments.  Names explicitly marked **proposed** are design targets, not current declarations.

## 1. Mathematical target

M8c should prove the substantive converse to M8b:

```text
properly discontinuous, cocompact subgroup of plane Euclidean motions
  ⇒
strong PlaneGroup on exactly the same motion subgroup.
```

For `X : GeometricWallpaperGroup`, write

```lean
Γ := X.carrier
L := (EuclideanMotion.translationVectors Γ).toIntSubmodule
```

The exact missing strong data are:

```lean
RankTwoLattice Plane
```

whose carrier is exactly `L`, and

```lean
Finite (EuclideanMotion.pointGroup Γ)
```

Once these have been proved, the target conversion should have the following type:

```lean
-- Proposed.
noncomputable def GeometricWallpaperGroup.toPlaneGroup
    (X : GeometricWallpaperGroup) : PlaneGroup
```

with unchanged carrier:

```lean
-- Proposed.
@[simp]
theorem GeometricWallpaperGroup.toPlaneGroup_carrier
    (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.carrier = X.carrier
```

The final geometric classification should reuse, rather than reproduce, the Version 1
classification.  Define the geometric standard model by the completed M8b conversion:

```lean
-- Proposed.
def WallpaperType.geometricModel (w : WallpaperType) :
    GeometricWallpaperGroup :=
  (WallpaperType.model w).toGeometricWallpaperGroup
```

After defining the direct geometric equivalence relation described in Section 3.6, the intended
classification statement is:

```lean
-- Proposed.
theorem geometric_classification (X : GeometricWallpaperGroup) :
    ∃! w : WallpaperType,
      GeometricWallpaperGroup.TextbookEquivalent
        X (WallpaperType.geometricModel w)
```

The corresponding quotient-level equivalence and cardinality corollary should then have the
shapes:

```lean
-- Proposed.
def WallpaperType.geometricEquivalenceClassEquiv :
    WallpaperType ≃ GeometricWallpaperGroup.EquivalenceClass

-- Proposed.
theorem GeometricWallpaperGroup.equivalenceClass_card_eq_seventeen :
    Nat.card GeometricWallpaperGroup.EquivalenceClass = 17
```

These are corollaries of the existing `classification`,
`PlaneGroup.textbookEquivalent_iff_equivalent`, and the conversion compatibility theorems.  They
must not duplicate the `5 + 3 + 9` case analysis.

## 2. Definition check

### 2.1 Current definitions

The approved geometric discreteness definition is:

```lean
def MotionSubgroup.IsDiscrete
    (Γ : Subgroup (EuclideanMotion Plane)) : Prop :=
  ProperlyDiscontinuousSMul Γ Plane
```

Mathlib exposes its compact-set formulation through the existing theorem:

```lean
theorem MotionSubgroup.isDiscrete_iff_compact_finite
    (Γ : Subgroup (EuclideanMotion Plane)) :
    MotionSubgroup.IsDiscrete Γ ↔
      ∀ {K L : Set Plane}, IsCompact K → IsCompact L →
        {γ : Γ | ((γ • ·) '' K ∩ L).Nonempty}.Finite
```

The approved cocompactness definition is:

```lean
def MotionSubgroup.IsCocompact
    (Γ : Subgroup (EuclideanMotion Plane)) : Prop :=
  ∃ K : Set Plane,
    IsCompact K ∧
      ⋃ γ : Γ, (γ • ·) '' K = Set.univ
```

The current geometric object is:

```lean
structure GeometricWallpaperGroup where
  carrier : Subgroup (EuclideanMotion Plane)
  isDiscrete : MotionSubgroup.IsDiscrete carrier
  isCocompact : MotionSubgroup.IsCocompact carrier
```

The orbit quotient is the standard quotient topology:

```lean
abbrev MotionSubgroup.OrbitSpace
    (Γ : Subgroup (EuclideanMotion Plane)) :=
  MulAction.orbitRel.Quotient Γ Plane
```

and the project already proves:

```lean
theorem MotionSubgroup.isCocompact_iff_compact_orbitSpace
    (Γ : Subgroup (EuclideanMotion Plane)) :
    MotionSubgroup.IsCocompact Γ ↔
      CompactSpace (MotionSubgroup.OrbitSpace Γ)
```

For the M8c proof, the most useful equivalent form is the existing compact representative
statement:

```lean
theorem MotionSubgroup.isCocompact_iff_exists_compact_orbit_representatives
    (Γ : Subgroup (EuclideanMotion Plane)) :
    MotionSubgroup.IsCocompact Γ ↔
      ∃ K : Set Plane, IsCompact K ∧
        ∀ x : Plane, ∃ γ : Γ, γ • x ∈ K
```

### 2.2 Sufficiency and standard meaning

The current definitions are sufficient and should remain unchanged.

- `ProperlyDiscontinuousSMul` is exactly the compact-set finite-intersection condition needed to
  obtain finite stabilizers, finite compact orbit preimages, and discreteness of the translation
  vectors.  It correctly permits finite stabilizers at rotation centers and along reflection
  axes.
- Compact-cover cocompactness gives the concrete witness needed to recover translations.  Its
  proved equivalence with compactness of `OrbitSpace` establishes correspondence with the
  standard quotient-space definition.
- The action is faithful without another field: `carrier` is a subgroup of actual affine
  isometry equivalences, acting by evaluation.
- Neither definition assumes a lattice, point-group finiteness, finite generation, or any
  conclusion of the Bieberbach theorem.

No minimal correction to `GeometricWallpaperGroup` is therefore proposed.

### 2.3 Alternatives considered

The following alternatives should not replace the approved definitions.

1. **Discrete topology on the subgroup as a subspace.**  Current mathlib does not provide the
   required natural topology or topological-group instance on `AffineIsometryEquiv`.  Building it
   would enlarge M8c without proving the rank-two or finite-point-group conclusions.
2. **Discrete subset of an ambient Euclidean-motion group.**  This has the same missing ambient
   topology and would require an additional equivalence with action-level proper discontinuity.
3. **`ProperSMul` after giving the abstract group the discrete topology.**  Mathlib can relate
   this to `ProperlyDiscontinuousSMul`, but it only repackages the current hypothesis.
4. **Compactness of the orbit quotient as the primary definition.**  This is already proved
   equivalent.  Direct quotient-topology manipulation is less useful than a compact set of orbit
   representatives for the inverse bridge.
5. **Covering-space methods.**  Mathlib's quotient-covering results require a free action.  The
   full wallpaper action need not be free, so this API becomes available only after isolating the
   translation subgroup and cannot recover that subgroup in the first place.

The audit found no need for a general topological group, a general locally compact group
abstraction, or a project-level axiomatization of a Bieberbach theorem.

## 3. Proof-route design

The recommended dependency order differs from the order in which the final `PlaneGroup` fields
are displayed: prove point-group finiteness first, then use it to transfer cocompactness to the
translation kernel, and only then prove that the translation group has full rank.

### 3.1 Existing algebraic and Euclidean-motion interfaces

The following current declarations are sufficient for the exact sequence:

```lean
EuclideanMotion.translationPart
EuclideanMotion.linearPart
EuclideanMotion.translation
EuclideanMotion.ext_parts
EuclideanMotion.eq_translation_of_linearPart_eq_one
EuclideanMotion.conjugate_translation

EuclideanMotion.translationVectors
EuclideanMotion.translationSubgroup
EuclideanMotion.translationEquiv
EuclideanMotion.pointGroup
EuclideanMotion.pointProjection
EuclideanMotion.pointProjection_ker
EuclideanMotion.pointGroup_exists_lift
EuclideanMotion.pointGroupExtension
```

In particular:

```lean
theorem EuclideanMotion.pointProjection_ker
    (Γ : Subgroup (EuclideanMotion Plane)) :
    (EuclideanMotion.pointProjection Γ).ker =
      EuclideanMotion.translationSubgroup Γ
```

means that `Finite (pointGroup Γ)` immediately gives finite index of the full translation
subgroup through `Subgroup.finiteIndex_ker`.

### 3.2 Point-group finiteness

Install `X.isDiscrete` as a `ProperlyDiscontinuousSMul Γ Plane` instance and choose a compact set
`K` meeting every orbit.  Proper discontinuity makes the following conceptual set finite:

```text
F_K = {g : Γ | (g '' K ∩ K).Nonempty}.
```

Let `A : pointGroup Γ` have positive determinant.

- If `A = 1`, it is handled separately.
- Otherwise choose a lift `g : Γ`.
- The lift is orientation-preserving and is not a translation, so the M8a motion decomposition
  makes it a rotation and supplies a fixed point `x`.
- Choose `h : Γ` with `h • x ∈ K`.
- The conjugate `q = h * g * h⁻¹` fixes `h • x`, hence belongs to `F_K`.
- Its linear part is `B * A * B⁻¹`, where `B` is the linear part of `h`.
- If `B` has positive determinant, two positive plane linear isometries commute, so this
  conjugate is `A`.
- If `B` has negative determinant, the existing two-dimensional conjugation lemma gives `A⁻¹`.

It follows that all positive point-group elements lie in:

```text
{1} ∪ pointProjection(F_K) ∪ pointProjection(F_K)⁻¹,
```

a finite set.  The negative part is either empty or, after fixing one negative element `s`, maps
injectively into the positive part by `A ↦ s * A`.  Consequently:

```lean
-- Proposed.
theorem MotionSubgroup.pointGroup_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    Finite (EuclideanMotion.pointGroup Γ)
```

Small compilation experiments confirmed the complete finite-set argument, including:

- positive plane linear isometries commute;
- positive conjugation fixes a positive element;
- negative conjugation sends it to its inverse;
- the positive and negative determinant parts combine to a finite point group.

The current M3 `orientationPreservingPointGroup` is parametrized by `PlaneGroup`, so it cannot be
used before constructing the strong object.  M8c should add a small subgroup-level determinant
predicate or local set of positive point elements in the new geometry file.  It must not modify
the M3 definition.

#### Rejected primary order

An alternative is to first prove that absence of a nonzero translation forces the whole group to
be finite, use cocompactness to obtain a nonzero translation, and then embed the point group into
the finite set of translation vectors of a fixed norm.  This route is mathematically valid, but
it needs additional common-fixed-point and injectivity lemmas before finite index is available.
The compact-rotation-center argument above proves point-group finiteness directly and is the
recommended production route.

### 3.3 Finite-index translation cover

After Section 3.2:

```lean
(EuclideanMotion.translationSubgroup Γ).FiniteIndex
```

follows from `pointProjection_ker`.  Mathlib supplies the finite-index kernel and quotient APIs,
but it does not supply the exact cocompactness transfer theorem needed here.

Choose a lift `r(A) : Γ` for every element `A` of the now finite point group.  If `K` is the
original compact set of orbit representatives, define:

```text
K_T = ⋃ A : pointGroup Γ, r(A)⁻¹ '' K.
```

This is a finite union of compact sets.  If `γ • x ∈ K`, take

```text
t = r(pointProjection γ)⁻¹ * γ.
```

Then `t` belongs to the kernel of `pointProjection`, hence is a pure translation, and
`t • x ∈ K_T`.  The project should package the result in a concrete translation-vector form:

```lean
-- Proposed.
theorem MotionSubgroup.exists_compact_translation_representatives
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    ∃ K : Set Plane, IsCompact K ∧
      ∀ x : Plane,
        ∃ t : (EuclideanMotion.translationVectors Γ).toIntSubmodule,
          (t : Plane) + x ∈ K
```

No general cocompact-action or topological-group abstraction is required for this finite-union
lemma.

### 3.4 Discreteness and full rank of the translation module

#### Discreteness

Proper discontinuity descends to the translation subgroup via:

```lean
Subgroup.properlyDiscontinuousSMul_of_le
```

For a compact set `C`, apply the compact-intersection condition to `{0}` and `C`.  Pure
translations taking `0` into `C` correspond injectively to translation vectors in `C`.
Therefore the subtype inclusion

```lean
Subtype.val :
  (EuclideanMotion.translationVectors Γ).toIntSubmodule → Plane
```

has finite preimage on every compact set.  The confirmed mathlib interface is:

```lean
tendsto_cofinite_cocompact_iff
Continuous.discrete_of_tendsto_cofinite_cocompact
```

It yields:

```lean
-- Proposed.
theorem MotionSubgroup.translationModule_discreteTopology
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ) :
    DiscreteTopology
      (EuclideanMotion.translationVectors Γ).toIntSubmodule
```

A second local-neighborhood proof using
`ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self` was also compiled as a feasibility
check.  The compact-preimage proof is preferred because it directly matches the approved
definition and the lattice API; only that route should be maintained in production.

#### Full real span

Let:

```lean
L := (EuclideanMotion.translationVectors Γ).toIntSubmodule
W := Submodule.span ℝ (L : Set Plane)
```

Use the compact translation representative set from Section 3.3.  If `W ≠ ⊤`, choose a nonzero
vector in `Wᗮ` and normalize it to `v`.  Every `t : L` has zero inner product with `v`, so
translation by `t` leaves the `v`-coordinate unchanged.  Compactness bounds the norm, hence the
absolute `v`-coordinate, of the representative set.  A sufficiently large scalar multiple of
`v` cannot be translated into that compact set, a contradiction.

Thus:

```lean
-- Proposed.
theorem MotionSubgroup.translationModule_span_eq_top
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    Submodule.span ℝ
      ((EuclideanMotion.translationVectors Γ).toIntSubmodule : Set Plane) = ⊤
```

This single theorem answers all three required degeneracy questions:

- a zero translation group has span `⊥`, so a nonzero translation must exist;
- a finite motion group has zero translation span and therefore cannot be cocompact;
- a rank-one translation group has a proper one-dimensional real span and is likewise excluded.

There is no need for three separate classification arguments.

### 3.5 Constructing the rank-two lattice and `PlaneGroup`

Discreteness and full span give:

```lean
IsZLattice ℝ L
```

Mathlib then supplies:

```lean
ZLattice.module_finite
ZLattice.module_free
ZLattice.rank
Module.Free.chooseBasis
Module.finrank_eq_card_chooseBasisIndex
Module.Basis.ofZLatticeBasis
```

A compilation experiment constructed:

```lean
RankTwoLattice Plane
```

from arbitrary:

```lean
(L : Submodule ℤ Plane) [DiscreteTopology L] [IsZLattice ℝ L]
```

by choosing an integer basis, using `ZLattice.rank` and `Plane.finrank` to reindex it by `Fin 2`,
and using `Module.Basis.ofZLatticeBasis` for ambient real linear independence.  This adapter is a
thin packaging layer, not a remaining mathematical risk.

The resulting production declarations should have shapes:

```lean
-- Proposed.
noncomputable def GeometricWallpaperGroup.translationLattice
    (X : GeometricWallpaperGroup) : RankTwoLattice Plane

-- Proposed.
theorem GeometricWallpaperGroup.translationLattice_carrier
    (X : GeometricWallpaperGroup) :
    X.translationLattice.carrier =
      (EuclideanMotion.translationVectors X.carrier).toIntSubmodule

-- Proposed.
noncomputable def GeometricWallpaperGroup.toPlaneGroup
    (X : GeometricWallpaperGroup) : PlaneGroup
```

The `PlaneGroup` carrier is `X.carrier`, the lattice equality is exact, and point-group
finiteness comes from Section 3.2.

### 3.6 Choice independence, round trips, and geometric equivalence

`RankTwoLattice` stores a selected integer basis.  Recovering that basis is noncomputable and is
not canonical.  M8c must therefore promise independence up to the approved equivalence, not
judgmental equality of `PlaneGroup` structures.

Two recovered strong structures on the same motion carrier are related by the identity group
isomorphism, which preserves the full translation subgroup.  The intended statements are:

```lean
-- Proposed.
theorem PlaneGroup.equivalent_of_carrier_eq
    {G H : PlaneGroup} (h : G.carrier = H.carrier) :
    PlaneGroup.Equivalent G H

-- Proposed.
theorem GeometricWallpaperGroup.toPlaneGroup_toGeometric
    (X : GeometricWallpaperGroup) :
    GeometricWallpaperGroup.TextbookEquivalent
      X X.toPlaneGroup.toGeometricWallpaperGroup

-- Proposed.
theorem PlaneGroup.toGeometric_toPlaneGroup
    (G : PlaneGroup) :
    PlaneGroup.Equivalent
      G G.toGeometricWallpaperGroup.toPlaneGroup
```

The second statement uses carrier equality; the third deliberately uses `PlaneGroup.Equivalent`
rather than equality because the recovered basis may differ from `G.translationLattice.basis`.

The final equivalence on geometric objects should be stated directly on their motion carriers,
not by exposing the chosen recovered bases.  The recommended structure is:

```lean
-- Proposed.
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

-- Proposed.
def GeometricWallpaperGroup.TextbookEquivalent
    (X Y : GeometricWallpaperGroup) : Prop :=
  Nonempty (GeometricWallpaperGroup.MotionTypePreservingIso X Y)
```

This is the geometric analogue of M8a and is independent of compact witnesses and lattice-basis
choices.  Adapters to the current strong `MotionTypePreservingIso` should be immediate after
`toPlaneGroup_carrier`.  As in M8a, preserving translations alone should imply preservation of
the other three motion types; nevertheless, the public textbook relation should state all four
types explicitly.

This choice is a specification point for owner approval.  Defining geometric equivalence merely
as `PlaneGroup.Equivalent X.toPlaneGroup Y.toPlaneGroup` would be shorter, but it would obscure
the geometric objects and the relation being classified behind a noncanonical conversion.

## 4. Risk analysis

### 4.1 Supported directly by current mathlib or project APIs

- affine isometry evaluation, `translationPart`, `linearPart`, multiplication, inverse, and
  translation conjugation;
- translation-kernel and point-group-range exact sequence;
- compact-set proper discontinuity, finite stabilizers, and inheritance by subgroups;
- finite-index kernel and finite quotient APIs;
- the standard orbit quotient and the project's compact-cover/compact-quotient equivalence;
- compactness and boundedness in the finite-dimensional plane;
- orthogonal complements in finite-dimensional inner-product spaces;
- `DiscreteTopology`, `IsZLattice`, finite/free lattice modules, lattice rank, and basis
  extension to the ambient real space;
- Version 1 equivalence, basis reframing, unique classification, quotient classes, and
  cardinality;
- M8a motion-type equivalence and M8b strong-to-geometric conversion.

### 4.2 Project lemmas still required

- finite set of elements fixing some point of a compact representative set;
- subgroup-level positive/negative determinant partition before a `PlaneGroup` exists;
- positive plane linear isometries commute;
- compact-rotation-center proof of finite point group;
- finite lift selection and compact-cover transfer to the translation kernel;
- compact-preimage proof of `DiscreteTopology L`;
- orthogonal-coordinate proof that the real span of translations is `⊤`;
- the `IsZLattice`-to-`RankTwoLattice` adapter;
- same-carrier equivalence, choice independence, round trips, and direct geometric equivalence
  adapters.

### 4.3 New mathematical content

The rotation-center finiteness argument and the full-span argument are a specialized
two-dimensional proof of the part of the first Bieberbach theorem needed here.  Mathlib source
search found no theorem for:

- Bieberbach groups;
- discrete cocompact Euclidean-isometry groups;
- crystallographic or space groups in this sense;
- automatic finite point group or full translation lattice;
- a general finite-index cocompactness transfer suitable for this action.

Therefore M8c does contain new mathematics, but the required proof is now localized and its key
lemmas have been validated in small compilation experiments.

### 4.4 APIs and abstractions not required

- a natural topological-group structure on `AffineIsometryEquiv`;
- general locally compact group theory;
- a general-dimensional Bieberbach theorem;
- a new crystallographic-group structure;
- finite generation or a Švarc--Milnor theorem;
- a new extension or cohomology abstraction;
- ordinary covering-space theory for the non-free full action.

### 4.5 Remaining risks

| Area | Risk | Reason |
| --- | --- | --- |
| Properness restricted to translations | Low | Existing subgroup instance/API. |
| Translation-module discreteness | Low | Both compact-preimage and neighborhood probes compiled. |
| `IsZLattice` to `RankTwoLattice` | Low | Complete adapter probe compiled. |
| Finite-index kernel | Low | `pointProjection_ker` plus existing typeclass inference. |
| Finite lift compact union | Medium | Finite bookkeeping and action orientation, but no new theorem. |
| Translation span `= ⊤` | Medium | Concrete inner-product proof compiled; production packaging remains. |
| Point-group finiteness | Medium-high | Main two-dimensional center-conjugation argument; a complete probe compiled. |
| Choice-independent round trip | Medium | Easy algebraically, but theorem strength must remain correctly stated. |
| Direct geometric equivalence | Specification review | Its exact public form determines the final classification statement. |

## 5. Staged implementation recommendation

The suggested Roadmap split is adjusted because finite point-group data is needed before the
clean finite-index translation-cover construction.

### M8c-a — local topology and finite point group

- create `WallpaperGroups/Geometry/GeometricToStrong.lean`;
- add subgroup-level determinant/orientation helpers without changing M3;
- add finite compact-intersection helper lemmas;
- prove the positive point part finite;
- prove `Finite (pointGroup Γ)`;
- add the finite-index kernel instance/theorem;
- add and test the `IsZLattice`-to-`RankTwoLattice` adapter.

This should be the first implementation checkpoint because point-group finiteness is the highest
risk theorem.

### M8c-b — recover the full rank-two translation lattice

- choose finite point-group lifts;
- transfer the compact representative set to the translation kernel;
- prove the translation module has `DiscreteTopology`;
- prove its real span is `⊤`;
- construct the exact full `RankTwoLattice`;
- explicitly record that zero- and rank-one translation cases are excluded.

### M8c-c — construct, compare, and classify

- construct `GeometricWallpaperGroup.toPlaneGroup` with identical carrier;
- prove choice independence and both round-trip compatibility statements;
- implement the approved direct geometric motion-type equivalence;
- prove equivalence with the reconstructed strong relation;
- derive `geometric_classification`;
- derive the quotient equivalence and seventeen-class cardinality.

Each substage should receive its own direct file compilation, full `lake build`, forbidden
placeholder scan, and review of any new foundational declaration.  No Version 1 classification
file should be rewritten.

## 6. Invariants

Completion of M8c must preserve all of the following.

1. `PlaneGroup` remains unchanged:

   ```lean
   structure PlaneGroup where
     carrier : Subgroup (EuclideanMotion Plane)
     translationLattice : RankTwoLattice Plane
     translationLattice_carrier :
       translationLattice.carrier =
         (translationVectors carrier).toIntSubmodule
     pointGroup_finite : Finite (pointGroup carrier)
   ```

   In particular, the lattice is the full translation subgroup, never a selected finite-index
   sublattice.

2. `GeometricWallpaperGroup`, `MotionSubgroup.IsDiscrete`, and
   `MotionSubgroup.IsCocompact` remain unchanged.
3. `RankTwoLattice` continues to store computational framing data.  Basis choice is invisible up
   to `PlaneGroup.Equivalent`, not forced to be canonical.
4. `TranslationPreservingIso`, `PlaneGroup.Equivalent`, and the M8a motion-type definitions remain
   unchanged.
5. `WallpaperType.model`, `classification`, `models_equivalent_iff`, and all Version 1 proofs
   remain unchanged.
6. `PlaneGroup.toGeometricWallpaperGroup` remains the canonical M8b conversion with definitionally
   unchanged carrier.
7. The completed relationship is:

   ```text
   strong PlaneGroup
     ⇒ geometric wallpaper group
     ⇒ strong PlaneGroup with the same carrier,
   ```

   with the strong round trip stated up to `PlaneGroup.Equivalent`.
8. The final geometric relation is an abstract group isomorphism preserving all four motion
   types.  It is not Euclidean conjugacy, affine conjugacy, similarity, or metric equivalence.
9. No rank-two lattice, finite point group, Bieberbach theorem, `sorry`, `admit`, new axiom, or
   `unsafe` implementation may be hidden in a hypothesis or placeholder.

## 7. Audit evidence and owner decisions

The audit inspected:

- `Mathlib/Topology/Algebra/ConstMulAction.lean`;
- `Mathlib/Topology/Algebra/Group/DiscontinuousSubgroup.lean`;
- `Mathlib/Topology/DiscreteSubset.lean`;
- `Mathlib/Topology/Covering/Quotient.lean`;
- `Mathlib/Topology/Algebra/ProperAction/Basic.lean`;
- `Mathlib/GroupTheory/Index.lean`;
- `Mathlib/Algebra/Module/ZLattice/Basic.lean`;
- the current Euclidean-motion, translation, point-group, exact-sequence, lattice, M3
  orientation, M8a motion-type, M8b geometry, equivalence, and classification files.

Compilation experiments confirmed:

- the exact namespaces and types of the APIs cited above;
- proper discontinuity inherited by `translationSubgroup Γ`;
- finite point group implying finite-index translation kernel;
- the complete center-conjugation finite-point-group argument;
- translation-module discreteness from proper discontinuity;
- the compact-translation-cover full-span argument;
- construction of the current `RankTwoLattice Plane` from `DiscreteTopology L` and
  `IsZLattice ℝ L`.

The project owner should decide whether to approve:

1. the current geometric definitions without modification;
2. the dependency order “finite point group, then translation compact cover, then full rank”;
3. the specialized two-dimensional route instead of a general Bieberbach/topological-group
   abstraction;
4. the direct carrier-level four-motion-type equivalence proposed in Section 3.6;
5. choice independence and the strong round trip only up to `PlaneGroup.Equivalent`;
6. the revised `M8c-a / M8c-b / M8c-c` implementation split in Section 5.

Until those points are approved, M8c's main proof must not begin.
