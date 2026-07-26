Review status: awaiting human approval

# M9 extension-theory design review

## 1. Scope

This is a design-only snapshot for the extension-theoretic track in
[`ROADMAP_V2.md`](ROADMAP_V2.md).  It does not start M9a or M9b, add a Lean
definition, or change any Version 1 or M8 theorem.

The audit was limited to the existing extension, shift, finite-coset, and
equivalence interfaces in this repository and the relevant APIs in the pinned
mathlib.  The principal recommendation is:

> M9 should use a small, explicit, dimension-independent API for normalized
> cocycles, coboundaries, twisted products, sections, and extension
> equivalences.  Mathlib's `GroupExtension` should remain the short-exact
> sequence foundation.  General `groupCohomology.H2` should be connected by an
> optional adapter, not made a critical dependency of the explicit core.

This follows the existing Version 2 roadmap and does not propose a second
classification of wallpaper groups.

## 2. Existing project infrastructure

### 2.1 M1: the canonical translation extension

M1 already supplies the required short exact sequence.  It must be reused
rather than duplicated.

In `WallpaperGroups/Invariants/Translation.lean`:

```lean
def translationEquiv (G : Subgroup (EuclideanMotion E)) :
    Multiplicative (translationVectors G) ≃*
      translationSubgroup G
```

identifies the additive translation vectors, with a multiplicative type tag,
with the kernel subgroup of pure translations.

In `WallpaperGroups/Invariants/PointGroup.lean`:

```lean
def pointActionHom (G : Subgroup (EuclideanMotion E)) :
    pointGroup G →*
      Multiplicative (AddAut (translationVectors G))
```

is already exactly the explicit action datum needed by a dimension-independent
extension API.

In `WallpaperGroups/Invariants/ExactSequence.lean`:

```lean
def pointGroupExtension (G : Subgroup (EuclideanMotion E)) :
    GroupExtension
      (translationSubgroup G) G (pointGroup G)
```

packages

```text
1 → translationSubgroup G → G → pointGroup G → 1.
```

The theorem

```lean
pointGroupExtension_conjAct_translationSubgroupElement
```

proves that the abstract conjugation action of this extension agrees with
`pointAction` after the translation-vector identification.  FD-003 already
records the decision to use mathlib's `GroupExtension` and not to assume a
splitting.

### 2.2 M4-M6: concrete extension calculations

The completed classification contains several special cases of the proposed
generic theory.

- `WallpaperGroups/Presentations/CyclicExtension.lean` uses
  `GroupExtension.Splitting` and mathlib's semidirect-product API for the zero
  cocycle case.  Its principal reusable declarations include
  `cyclicSplitting`, `splitExtensionMulEquiv`, `splitPlaneGroupIso`, and
  `cyclicExtensionIso`.
- `WallpaperGroups/Presentations/ReflectionExtension.lean` stores the square
  translation of a reflection lift in `ReflectionExtensionData.shift`.
  `ReflectionExtensionData.adjust` changes the lift by a left translation and
  changes the square shift by the order-two norm.  The theorem
  `reflectionExtensionIsoOfShiftDifference` is the `C₂` instance of
  "coboundary-related factors give equivalent extensions."
- `WallpaperGroups/Presentations/DihedralExtension.lean` has a normalized
  section in `DihedralExtensionData.lift`, with `lift_one : lift 1 = 1`.
  Its factor is

  ```lean
  dihedralFactor c q r
  ```

  obtained from

  ```text
  lift(q) * lift(r) * lift(qr)⁻¹.
  ```

  `dihedralFactor_one_left` and `dihedralFactor_one_right` prove normalization,
  and `dihedralDecode_mul` fixes the multiplication convention

  ```text
  (t, q) * (u, r) =
    (t + q • u + dihedralFactor(q, r), q r).
  ```

  The file does not yet bundle `dihedralFactor` as a 2-cocycle or prove the
  general section-change formula.
- `WallpaperGroups/Presentations/TwoReflectionExtension.lean` constructs the
  canonical `wordLift` and `wordFactor`.  The theorem
  `dihedralFactor_toDihedralExtensionData` identifies that explicit table with
  `dihedralFactor`, while `wordFactor_natural` proves transport under matched
  action and generator data.  `twoReflectionExtensionIsoOfShiftClasses`
  performs a generator-level coboundary adjustment, but it is intentionally
  specialized to the two-reflection classification.

These declarations are regression examples and adapter targets.  M9 should not
replace their proofs.

### 2.3 M5: quotient-valued shift classes

`WallpaperGroups/Invariants/ShiftClass.lean` already defines the finite norm

```lean
finiteNormHom G h q (t) =
  ∑ i ∈ Finset.range q, pointAction G.carrier (h ^ i) t
```

and the quotient

```lean
ShiftClassGroup G h q hq =
  fixedTranslationSubgroup G h ⧸
    normTranslationSubgroup G h q hq.
```

Thus the existing invariant is exactly

```text
T^h / N_h(T).
```

`liftPowerFixedTranslation` supplies the fixed representative,
`shiftClass_lift_independent` proves lift independence, and
`shiftClass_natural` plus `shiftClassEquivOfIntertwining` provide the existing
functoriality pattern.

The sign convention is already explicit:

```text
[x] = [y]  ↔  ∃ t, x = N_h(t) + y.
```

For a cyclic quotient generated by `h`, this is the standard concrete
description of `H²(C_q, T)`.  The current API is deliberately an
element-and-period interface: it assumes `h ^ q = 1`, not that `q` is positive
or the exact order.  M9 should add an interpretation theorem rather than
change this useful API.

### 2.4 Finite-coset models

`WallpaperGroups/Models/DihedralModels.lean` contains:

```lean
structure FiniteCosetData (P : Type*) [Group P] [Finite P] where
  lattice : RankTwoLattice Plane
  linearRep : P →* (Plane ≃ₗᵢ[ℝ] Plane)
  linearRep_injective : Function.Injective linearRep
  preserves_lattice :
    ∀ p : P, linearRep p ∈ latticeStabilizer lattice
  shift : P → Plane
  shift_one_mem : shift 1 ∈ lattice.carrier
  cocycle_mem : ∀ p q : P,
    shift p + linearRep p (shift q) - shift (p * q) ∈
      lattice.carrier
```

The field name `cocycle_mem` must not obscure the two different objects:

1. `p ↦ shift p mod lattice` is a `Plane / lattice`-valued 1-cocycle.
2. The lattice-valued defect

   ```text
   shift p + p • shift q - shift (p q)
   ```

   is the factor set, hence the prospective 2-cocycle of the group extension.

Only `shift 1 ∈ lattice.carrier` is stored; raw `shift 1 = 0` is not a field.
The generic adapter must normalize the section, for example by replacing the
raw representative by `shift p - shift 1`, before claiming a normalized
factor.  It must not silently strengthen `FiniteCosetData`.

The rank-two lattice, faithful plane representation, and finiteness of `P` are
model-layer data.  None belongs in the generic M9 core.

### 2.5 M8: access from geometric wallpaper groups

M8 adds no competing extension invariant.  Its role is to make the M1
extension available from either formulation.

```lean
noncomputable def GeometricWallpaperGroup.toPlaneGroup
    (X : GeometricWallpaperGroup) : PlaneGroup
```

has exactly the same motion carrier, and
`toPlaneGroup_choice_independent` removes recovered-basis choices through
`PlaneGroup.Equivalent`.  Moreover,

```lean
GeometricWallpaperGroup.textbookEquivalent_iff_equivalent
```

identifies the direct geometric relation with strong equivalence after
conversion.

Consequently the geometric adapter for M9 should be thin:

```text
X
  ↦ X.toPlaneGroup
  ↦ pointGroupExtension X.toPlaneGroup.carrier.
```

The dimension-independent M9 core should not import geometric topology,
`Plane`, or the Bieberbach bridge.

## 3. Current mathlib support

The audit used the repository's pinned mathlib `v4.32.1`.

### 3.1 `GroupExtension`

The confirmed modules are:

- `Mathlib.GroupTheory.GroupExtension.Defs`
- `Mathlib.GroupTheory.GroupExtension.Basic`
- `Mathlib.GroupTheory.SemidirectProduct`

Useful declarations include:

- `GroupExtension`, `GroupExtension.Section`,
  `GroupExtension.Splitting`, and `GroupExtension.Equiv`;
- `GroupExtension.conjAct`;
- `GroupExtension.surjInvRightHom`;
- the section range lemmas such as
  `GroupExtension.Section.mul_mul_mul_inv_mem_range_inl`;
- `GroupExtension.Section.equivComp`;
- `GroupExtension.Equiv.ofMonoidHom`; and
- the splitting/semidirect-product equivalences.

Important limitations are:

- `Section` is only a set-theoretic right inverse and need not map `1` to `1`;
- `GroupExtension.Equiv` fixes the two endpoint types;
- semidirect products cover only split extensions; and
- there is no general factor-set, twisted-product, or extension-classification
  construction.

The source TODO in `GroupExtension/Defs.lean` explicitly lists the bijection
between abelian-kernel extension classes and `groupCohomology.H2` as future
work.

### 3.2 Low-degree group cohomology

Mathlib does contain general group cohomology.  The relevant confirmed modules
are:

- `Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree`
- `Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality`
- `Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`

The low-degree file exposes the exact explicit formulas:

```lean
groupCohomology.IsCocycle₂ (f : G × G → A) :=
  ∀ g h j,
    f (g * h, j) + f (g, h) =
      g • f (h, j) + f (g, h * j)
```

and

```lean
groupCohomology.IsCoboundary₂ (f : G × G → A) :=
  ∃ b : G → A, ∀ g h,
    g • b h - b (g * h) + b g = f (g, h).
```

It also provides `groupCohomology.H2`, `H2π`, `H2π_eq_iff`,
`mapCocycles₂`, and `H2π_comp_map`.  An additive commutative group can be
viewed as a `ℤ`-module, so a later adapter through
`Rep.ofDistribMulAction ℤ H T` is available.

However:

- these cocycles are not normalized;
- the API is expressed through representations, `ModuleCat`, and homological
  complexes and is largely noncomputable;
- the source TODO explicitly says that the relation between `H2` and group
  extensions is missing; and
- no executable general finite-group `H²` enumeration is supplied.

For a finite cyclic group, `groupCohomologyIsoEven` and
`groupCohomologyπEven_eq_iff` compute positive even cohomology by the fixed
subgroup modulo the norm range.  This is an excellent comparison target for
`ShiftClassGroup`, but it does not remove the need for the project's explicit
extension layer.

### 3.3 Decision on general cohomology

General group cohomology should not be on the M9 critical path.

The explicit core should have no dependency on bar resolutions, homological
complexes, or `ModuleCat`.  A separate adapter may prove:

- the project cocycle law is `groupCohomology.IsCocycle₂`;
- the project section-change term is
  `groupCohomology.IsCoboundary₂`;
- the explicit quotient maps to `groupCohomology.H2`; and
- in the finite cyclic case, the resulting class agrees with the existing
  `ShiftClassGroup`.

This preserves a rigorous connection to standard `H²` while keeping the data
layer suitable for later computation.

## 4. Proposed explicit conventions

The following conventions match every existing project formula and should be
fixed before M9 implementation.

Let:

```text
H  be a group,
T  be an additive commutative group,
ρ : H →* Multiplicative (AddAut T)
```

be the prescribed left action.

1. A section is written on the right:

   ```text
   element = inl(t) * s(h).
   ```

2. Its factor is defined by:

   ```text
   s(g) * s(h) = inl(c(g,h)) * s(gh).
   ```

3. The normalized conditions are:

   ```text
   c(1,h) = 0,
   c(g,1) = 0.
   ```

4. Associativity gives:

   ```text
   c(g,h) + c(gh,k) =
     g • c(h,k) + c(g,hk).
   ```

5. The twisted product is:

   ```text
   (t,g) * (u,h) =
     (t + g • u + c(g,h), gh).
   ```

6. A normalized section change is made by left translation:

   ```text
   s'(g) = inl(b(g)) * s(g),
   b(1) = 0.
   ```

   Its factor is:

   ```text
   c'(g,h) =
     b(g) + g • b(h) + c(g,h) - b(gh).
   ```

   Thus the chosen convention is `c' = c + δb`.

7. The corresponding twisted-product isomorphism is:

   ```text
   (t,g) ↦ (t - b(g), g).
   ```

These signs agree with `dihedralDecode_mul`,
`ReflectionExtensionData.adjust`, `FiniteCosetData.cocycle_mem`,
`liftDifferenceTranslation`, and
`shiftClass_mk_eq_mk_iff_exists_norm_add`.  They should become dedicated
regression tests.

## 5. Proposed project API

All names in this section are design targets rather than existing
declarations.

### 5.1 Actions and normalized cocycles

The public core should take the action as explicit data

```lean
ρ : H →* Multiplicative (AddAut T)
```

rather than rely exclusively on a global `DistribMulAction` instance.  This
matches `pointActionHom`, avoids typeclass collisions when comparing multiple
actions, and makes an enumerated integral representation an ordinary value.
A thin local adapter can install the corresponding scalar action when a
mathlib theorem requires it.

A proposed `NormalizedCocycle ρ` stores:

- `c : H → H → T`;
- the two normalization equations; and
- the cocycle equation from Section 4.

A normalized 1-cochain stores `b : H → T` and `b 1 = 0`.  Its coboundary uses
the fixed formula above.  `Cohomologous ρ c d` should mean that
`d = c + δb` for some normalized cochain `b`.

This explicit equivalence relation is the primary quotient needed by the
project.  A categorical `H²` object is not required to state or prove the
extension classification.

### 5.2 Extensions with a prescribed action

The generic extension layer should wrap, not replace:

```lean
GroupExtension (Multiplicative T) E H.
```

It must also record that conjugation induces the prescribed action.  A direct
compatibility field can have the mathematical content:

```text
inl(ρ(rightHom(e))(t)) =
  e * inl(t) * e⁻¹.
```

This avoids treating `GroupExtension.conjAct : E →* MulAut N` as though it
were already an action of the quotient.  For an abelian kernel it descends,
but that descent must be proved or included as compatibility data.

A proposed `NormalizedSection` should extend mathlib's
`GroupExtension.Section` with `s 1 = 1`.  There should be:

- a normalization operation for any section;
- factor extraction from a normalized section;
- proofs of normalization and the cocycle identity;
- the explicit section-change/coboundary theorem; and
- naturality under extension equivalence.

Choice used to obtain a section may be noncomputable.  The resulting
classification statement must be independent of the chosen section.

### 5.3 Two equivalence levels

Two notions must remain distinct.

1. **Fixed endpoints and fixed action.**  Here mathlib's
   `GroupExtension.Equiv` is the correct middle-group equivalence.  This is the
   level classified by the explicit cocycle quotient.
2. **Transported endpoints.**  Comparisons between different plane groups or
   future catalog entries also require:

   ```text
   eT : T ≃+ T',
   eH : H ≃* H',
   ```

   an action-intertwining equation, a middle-group equivalence, and two
   commuting endpoint squares.

The second layer may be a small heterogeneous wrapper, or it may transport
the endpoints first and then reuse `GroupExtension.Equiv`.  It must not be
conflated with equality in one fixed `H²`.  Existing
`TranslationPreservingIso.translationVectorEquiv`,
`pointGroupEquiv`, and `translationVector_pointAction` supply precisely the
required data for the wallpaper adapter.

### 5.4 Twisted products and classification

For `c : NormalizedCocycle ρ`, M9b should define a new type over `T × H` with
the multiplication from Section 4 and prove:

- its group laws;
- the canonical injection and projection;
- its canonical `GroupExtension`;
- its induced action is `ρ`;
- its canonical normalized section has factor `c`; and
- `c = 0` recovers the existing semidirect-product case.

For an extension over `ρ` with normalized section `s`, normal-form decoding

```text
(t,h) ↦ inl(t) * s(h)
```

should be a group equivalence from the twisted product associated to the
extracted factor.

The final fixed-action theorem should state that:

- cohomologous normalized cocycles give equivalent extensions; and
- an endpoint-preserving extension equivalence gives the corresponding
  coboundary relation.

The theorem classifies extensions with the prescribed action.  It does not
classify different actions or quotient them by lattice-basis changes.

## 6. Suggested implementation stages

### M9a: interpretation of the completed two-dimensional code

M9a should establish the conventions with the smallest generic factor-set
layer needed for interpretation, then add the following adapters.

1. Rebase `pointGroupExtension` along `translationEquiv` so its left endpoint
   is `Multiplicative (translationVectors G.carrier)`.
2. Extract the factor of a normalized section and prove its cocycle identity,
   section-change formula, and naturality.
3. Prove `dihedralFactor` and `wordFactor` are instances of that generic
   factor.
4. Normalize `FiniteCosetData.shift`, bundle its lattice-valued defect, and
   prove:
   - the quotient-valued shift is a 1-cocycle;
   - the lattice defect is the extension factor; and
   - changing representatives changes that factor by the explicit
     coboundary.
5. Restrict to a finite cyclic subgroup and prove that the period evaluation
   of the factor is the existing `liftPowerFixedTranslation`, hence that the
   resulting quotient class is `shiftClass`.
6. Optionally compare this last result with mathlib's finite-cyclic
   `groupCohomologyπEven`; this comparison must not block the explicit
   `shiftClass` theorem.

No M4-M7 classifier should be rewritten in cohomological language.

### M9b: dimension-independent extension theory

M9b can then extract the generic layer:

1. explicit action, normalized cocycle, normalized cochain, coboundary, and
   cohomologous relation;
2. extension-over-action and normalized-section APIs;
3. twisted product and its canonical exact sequence;
4. section extraction and reconstruction;
5. both directions between cocycle equivalence and fixed-endpoint extension
   equivalence;
6. heterogeneous endpoint transport and the wallpaper adapters; and
7. a thin free-abelian specialization sufficient to state inputs

   ```text
   T ≃+ (Fin n → ℤ)
   ```

   together with a finite integral action.

A reasonable source split is:

```text
WallpaperGroups/Extensions/
  Action.lean
  NormalizedCocycle.lean
  FactorSet.lean
  TwistedProduct.lean
  Section.lean
  Classification.lean
  GroupCohomologyAdapter.lean
  WallpaperAdapters.lean
```

Stable Version 1 files should not be moved merely to fit this layout.

## 7. Future verified space-group enumeration

### 7.1 Worth formalizing in M9

The following abstractions directly support future reuse and belong in M9:

- arbitrary `H`, additive commutative `T`, and an explicit action `ρ`;
- normalized cocycles and cochains with executable pointwise formulas;
- twisted products and endpoint-preserving equivalences;
- action transport through compatible `eT` and `eH`;
- the specialization `T ≃+ ℤ^n`;
- a finite group with an integral action as an input type; and
- comparison theorems connecting the two-dimensional code to the generic
  theory.

Finiteness of `H` and finite rank of `T` should not be assumptions of the
basic cocycle or twisted-product constructions.

### 7.2 Required later, but outside M9

A verified, certificate-producing higher-dimensional enumerator would also
need:

- a complete enumeration of finite subgroups of `GL_n(ℤ)` up to integral
  conjugacy;
- computable finite cochain complexes and integer matrices;
- certified kernel/image and Smith-normal-form computations;
- the action of compatible endpoint automorphisms and normalizers on
  extension classes;
- orbit representatives with soundness, completeness, and no-duplicate
  proofs;
- affine/crystallographic realization certificates; and
- dimension-specific classification data.

Mathlib's structural Smith-normal-form and homology results are useful for
existence theorems but are not by themselves an executable catalog algorithm.
M9 should expose clean input and equivalence types without pretending to
implement these later layers.

### 7.3 Keep as mathematical explanation only

The following should remain explanatory in M9 unless a later theorem needs
them:

- the historical statement that abelian-kernel extensions are classified by
  `H²`;
- general Bieberbach theorems;
- CARAT or other database formats;
- the three-dimensional list of 230 groups;
- OEIS enumeration claims;
- a general-purpose group-cohomology library; and
- normalizer and finite-integral-point-group enumeration algorithms.

## 8. Risks and human-review decisions

The owner should review the following before M9a implementation.

1. **Action representation.**  The recommendation is an explicit
   `H →* Multiplicative (AddAut T)` public parameter, with local typeclass
   adapters only where mathlib needs them.
2. **Sign convention.**  Confirm `c' = c + δb` for the left section change
   `s'(g) = inl(b(g))s(g)`, and the resulting coordinate map
   `(t,g) ↦ (t-b(g),g)`.
3. **Normalized sections.**  Mathlib sections are not normalized; M9 must add
   a wrapper or normalization operation rather than assume `s 1 = 1`.
4. **Prescribed action.**  The quotient action must be proved to agree with
   `ρ`; it must not be inferred by treating the middle-group conjugation
   action as quotient-valued without proof.
5. **Equivalence scope.**  Fixed-endpoint extension equivalence and
   heterogeneous endpoint transport are separate layers.
6. **Finite-coset interpretation.**  The torus-valued 1-cocycle and the
   lattice-valued 2-cocycle must remain distinct, and raw `shift 1` must be
   normalized explicitly.
7. **Cyclic comparison strength.**  M9a must prove an explicit theorem relating
   the restricted extension data to `shiftClass`; an abstract prose analogy
   with `H²` is insufficient.
8. **General `H²`.**  The recommended mathlib comparison is an adapter and
   optional validation theorem, not the definition of the core extension
   class.
9. **Computability boundary.**  Choosing a section from an arbitrary
   extension may be noncomputable.  Explicit cocycles, finite actions, and
   later certificate inputs should nevertheless remain ordinary inspectable
   data.

## 9. Invariants

Under this design:

- `PlaneGroup`, `TranslationPreservingIso`, and the Version 1 classifier are
  unchanged;
- the M8 geometric definitions and classification are unchanged;
- `pointGroupExtension` remains the canonical two-dimensional exact sequence;
- `shiftClass` remains the public cyclic/reflection invariant used by M5-M7;
- noncanonical sections affect factors only by the proved coboundary relation;
- the generic core contains no `Plane`, Euclidean metric, rank-two normal
  form, crystallographic order, or wallpaper label; and
- no claim of a higher-dimensional space-group classification is made.

M9a and M9b remain unstarted until this design receives human approval.
