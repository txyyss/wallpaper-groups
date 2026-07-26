Review status: awaiting human approval

# M9b extension-equivalence design review

## 1. Scope and decision summary

This is a design-only snapshot for M9b.  It does not implement M9b, modify an
existing Lean declaration, or change any Version 1, M8, or M9a theorem.

The audit covered:

- mathlib's `GroupExtension`, `GroupExtension.Equiv`, section, and splitting
  APIs at the pinned mathlib revision;
- the M9a explicit action, cocycle, twisted-product, and normalized-section
  modules;
- the M1 point-group extension;
- the M4--M6 cyclic, reflection, dihedral, and finite-coset constructions;
- the M5 quotient-valued `ShiftClassGroup`; and
- the boundary with mathlib's `groupCohomology.H2`.

A temporary Lean probe confirmed that the fixed-endpoint equivalence,
twisted-product reconstruction, section transport, and pairwise classification
route described below compiles against the current dependencies.  The probe
was not added to the repository.

The recommended M9b result is:

> For a fixed explicit action `ρ`, every extension over `ρ` is
> endpoint-preservingly equivalent to the twisted product of the cocycle
> extracted from any normalized section, and two such extensions are
> endpoint-preservingly equivalent exactly when their cocycles differ by the
> explicit M9a coboundary.

This gives the full mathematical content of

```text
extensions with fixed endpoints and fixed action, modulo equivalence
  ↔
normalized cocycles, modulo coboundaries
```

without constructing a universe-sensitive quotient type containing every
possible middle-group type.

## 2. Fixed-endpoint extension equivalence

### 2.1 Reuse mathlib's exact notion

For

```lean
S  : GroupExtension N E  H
S' : GroupExtension N E' H
```

mathlib already defines:

```lean
S.Equiv S'
```

as a middle-group equivalence `E ≃* E'` satisfying:

```text
equiv (S.inl n) = S'.inl n
S'.rightHom (equiv e) = S.rightHom e.
```

Thus both endpoint maps are literally the identity.  This is exactly the
endpoint-preserving equivalence needed for the fixed-action classification.
M9b must not introduce a competing fixed-endpoint structure.

The confirmed supporting declarations are:

```lean
GroupExtension.Equiv.map_inl
GroupExtension.Equiv.rightHom_map
GroupExtension.Equiv.refl
GroupExtension.Equiv.symm
GroupExtension.Equiv.trans
GroupExtension.Equiv.ofMonoidHom
GroupExtension.Section.equivComp
```

### 2.2 Coboundary coordinate changes

M9a already provides:

```lean
TwistedProduct.changeByMulEquiv
TwistedProduct.changeByMulEquiv_inl
TwistedProduct.rightHom_changeByMulEquiv
```

for the coordinate map:

```text
(t, g) ↦ (t - b(g), g)
```

from `c` to `c.changeBy b`.  M9b should bundle these three facts directly as:

```lean
TwistedProduct.changeByExtensionEquiv
    (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) :
  (TwistedProduct.toGroupExtension c).Equiv
    (TwistedProduct.toGroupExtension (c.changeBy b))
```

This is the forward implication from an explicit coboundary to extension
equivalence.  `GroupExtension.Equiv.ofMonoidHom` is unnecessary here because
the computable `MulEquiv` already exists.

### 2.3 Transporting normalized sections

M9b should lift `GroupExtension.Section.equivComp` to normalized sections:

```lean
NormalizedSection.equivComp
```

A group equivalence maps `1` to `1`, so normalization is preserved.  If
`e : S.Equiv S'`, transporting a normalized section `s` across `e` must satisfy
the exact, not merely cohomological, naturality statements:

```text
factor (e ∘ s) g h = factor s g h
toCocycle (e ∘ s) = toCocycle s.
```

These statements follow from `e.map_inl`, `e.rightHom_map`,
`NormalizedSection.inl_factor`, and injectivity of the target kernel map.

Comparing an arbitrary target section with the transported source section then
uses the existing theorem:

```lean
NormalizedSection.toCocycle_change
```

to produce the required coboundary.

## 3. Reconstruction and fixed-action classification

### 3.1 Twisted-product reconstruction

Let:

```lean
X : ExtensionOverAction (E := E) ρ
s : NormalizedSection X.toGroupExtension
```

and let `c := s.toCocycle X`.  The normal-form map is:

```text
(t, h) ↦ X.inl (Multiplicative.ofAdd t) * s(h).
```

Its multiplicativity follows from:

```lean
NormalizedSection.mul_eq_inl_factor_mul
NormalizedSection.conjugation_inl
```

and the multiplication of `TwistedProduct c`.  The map fixes the kernel and
commutes with the quotient projection.  Therefore the preferred construction
is:

```lean
GroupExtension.Equiv.ofMonoidHom
```

which supplies the inverse without adding another noncanonical coordinate
choice.  The proposed result is:

```lean
NormalizedSection.twistedProductExtensionEquiv :
  (TwistedProduct.toGroupExtension (s.toCocycle X)).Equiv
    X.toGroupExtension
```

The inverse equivalence may be exported for the verbal direction “original
extension to twisted product,” but only one proof should be maintained.

### 3.2 Canonical twisted-product theorem

The first main theorem should have this complete shape:

```lean
theorem TwistedProduct.extensionEquiv_iff_cocycleCohomologous
    (c d : NormalizedCocycle ρ) :
    Nonempty
        ((TwistedProduct.toGroupExtension c).Equiv
          (TwistedProduct.toGroupExtension d)) ↔
      CocycleCohomologous c d
```

The reverse implication uses `changeByExtensionEquiv`.  For the forward
implication, transport the canonical section of `c` across the supplied
extension equivalence, compare it with the canonical section of `d`, and use:

```lean
TwistedProduct.canonicalSection_toCocycle
NormalizedSection.toCocycle_change
```

This also verifies the M9a sign convention:

```text
d = c + δb
(t, g) ↦ (t - b(g), g).
```

### 3.3 Arbitrary extensions

For two extensions over the same action:

```lean
X : ExtensionOverAction (E := E)  ρ
Y : ExtensionOverAction (E := E') ρ
```

and explicit normalized sections `s` and `t`, M9b must prove:

```lean
Nonempty (X.toGroupExtension.Equiv Y.toGroupExtension) ↔
  CocycleCohomologous (s.toCocycle X) (t.toCocycle Y)
```

The backward direction composes:

```text
reconstruction(X, s)⁻¹
  → coboundary coordinate equivalence
  → reconstruction(Y, t).
```

The forward direction is section transport followed by the M9a section-change
theorem.

### 3.4 Quotient-valued class, but no quotient of all middle types

M9b should give a short name to the already defined cocycle setoid quotient,
for example:

```lean
abbrev CocycleClass (ρ : AdditiveAction H T) :=
  Quotient (CocycleCohomologous.setoid ρ)
```

It may define a noncomputable class of an arbitrary extension by normalizing
`X.toGroupExtension.surjInvRightHom` and taking the quotient class of its
cocycle.  The public invariant is the quotient class, not the chosen cocycle.
M9b must prove:

- independence from the normalized section;
- invariance under endpoint-preserving extension equivalence;
- every extension is equivalent to a twisted product realizing its class; and
- every cocycle class is realized by its canonical twisted product.

The public pairwise classifier should then state:

```text
X and Y are endpoint-preservingly equivalent
  ↔
their cocycle classes are equal.
```

M9b should not bundle every possible middle type into a large
`BundledExtension` merely to manufacture a literal equivalence between two
quotient types.  Such a construction introduces universe and instance
bookkeeping without strengthening the pairwise theorem.  It can be added
later if an actual consumer needs that particular type.

## 4. Heterogeneous endpoint and action transport

Fixed-action classification and endpoint transport are separate layers.
Mathlib's `GroupExtension.Equiv` cannot change `T` or `H`.

M9b should add a small dimension-independent transport layer containing:

```text
eT : T ≃+ T'
eH : H ≃* H'
```

and the action-intertwining law:

```text
eT (ρ(h)(t)) = ρ'(eH(h))(eT(t)).
```

The cocycle transport has the mathematical formula:

```text
c'(eH(g), eH(h)) = eT(c(g, h)).
```

M9b must transport normalized cochains as well and prove that transport
commutes with:

- `NormalizedCochain.coboundary`;
- `NormalizedCocycle.changeBy`; and
- `CocycleCohomologous`.

For extensions, a heterogeneous equivalence should additionally carry:

```text
eE : E ≃* E'
```

and the two endpoint squares:

```text
eE (inl(t)) = inl'(eT(t))
rightHom'(eE(e)) = eH(rightHom(e)).
```

This wrapper must not replace `GroupExtension.Equiv` in the fixed-endpoint
layer.  After endpoint relabeling and cocycle transport, the fixed-action
classification should be reused rather than reproved.

M9b does not quotient extension classes by all compatible endpoint
automorphisms.  Such normalizer/orbit quotients belong to a future enumerator.

## 5. Connections to existing project code

### 5.1 M1 and M8

M1 remains the only short-exact-sequence foundation:

```lean
EuclideanMotion.pointGroupExtension
```

M9a already supplies:

```lean
EuclideanMotion.pointGroupVectorExtension
EuclideanMotion.pointGroupExtensionOverAction
```

by relabeling the kernel along `translationEquiv` and proving compatibility
with `pointActionHom`.  M9b should consume these declarations and must not
rebuild the exact sequence.

M8 adds no competing extension object.  A geometric wallpaper group reaches
the same M1 extension through:

```lean
GeometricWallpaperGroup.toPlaneGroup
```

whose motion carrier is unchanged.  Any geometric-facing M9 corollary should
be a late adapter through that conversion; the dimension-independent core
must not import M8 topology or plane geometry.

### 5.2 M4: split cyclic extensions

M4 already has:

```lean
cyclicSplitting
splitExtensionMulEquiv
splitPlaneGroupIso
cyclicExtensionIso
```

The generic adapter should turn a `GroupExtension.Splitting` into a
`NormalizedSection` and prove that its cocycle is zero.  This identifies the
M4 split case with the zero-cocycle twisted product.  A named M4 corollary is
useful as a regression theorem, but no cyclic classification proof should be
rewritten.

### 5.3 M5: cyclic period and `ShiftClassGroup`

For a normalized cocycle and `h ^ q = 1`, define the explicit period
evaluation:

```text
period(c, h, q) = ∑ i in range q, c(h^i, h).
```

M9b must prove:

1. `period(c, h, q)` is fixed by `h`;
2. changing `c` by `b` changes the period by the finite norm of `b(h)`;
3. the quotient class of the period therefore depends only on the cocycle
   class;
4. for a normalized extension section `s`, the kernel coordinate of
   `(s h)^q` is the period of `s.toCocycle`; and
5. for `pointGroupExtensionOverAction`, this quotient class is exactly the
   existing:

   ```lean
   shiftClass G h q hq lift lift_projection.
   ```

This proves that M5's lift independence is the cyclic coboundary phenomenon.
The existing `finiteNormHom`, `ShiftClassGroup`, `shiftClass`,
`shiftClass_lift_independent`, and `shiftClass_natural` remain the public
Version 1 API and are not replaced.

For `q = 2`, the same theorem interprets
`ReflectionExtensionData.adjust` and
`reflectionExtensionIsoOfShiftDifference`; only a thin sign-regression
corollary is needed.

### 5.4 M6: dihedral factors

M9a already provides:

```lean
dihedralNormalizedSection
dihedralNormalizedCocycle
dihedralNormalizedCocycle_apply
dihedralFactor_cocycle
```

and Version 1 already identifies `wordFactor` with `dihedralFactor` through:

```lean
dihedralFactor_toDihedralExtensionData
```

The M9b reconstruction theorem should apply directly to this normalized
section.  An optional named corollary may expose `wordFactor` as the same
cocycle, but M9b must not rewrite `dihedralExtensionIso`,
`twoReflectionExtensionIsoOfShiftClasses`, or any M6 classifier.

### 5.5 `FiniteCosetData`

The two cohomological objects in `FiniteCosetData` must remain distinct:

1. `p ↦ [shift p]` is a `Plane / lattice`-valued `1`-cocycle;
2. the lattice-valued defect is a `2`-cocycle for the extension.

The raw data only assumes:

```lean
shift_one_mem : shift 1 ∈ lattice.carrier
```

not `shift 1 = 0`.  Therefore M9b must not use `shift` directly as a
normalized cochain or section coordinate.

Before comparing the finite-coset factor with the M1 point-group extension,
M9b should package:

```lean
finiteCosetPointElement D
```

as an equivalence from `P` to the point group of
`finiteCosetPlaneGroup D`.  Injectivity and the point-group range computation
already exist.  The quotient endpoint should then be transported along this
equivalence; `P` must not be treated as judgmentally equal to the point-group
subtype.

The quotient-valued `1`-cocycle may use the raw class `[shift p]`; its value at
`1` is zero in the quotient by `shift_one_mem`, and its cocycle law follows
from `cocycle_mem`.  The action descends because `linearRep` preserves the
lattice.

For the lattice-valued factor, first normalize:

```text
shift⁰(p) = shift(p) - shift(1).
```

Then:

```text
factor(p, q) =
  shift⁰(p) + linearRep(p)(shift⁰(q)) - shift⁰(pq)
```

is normalized and lies in the lattice.  It should be defined as a value of
`D.lattice.carrier` and proved equal to the generic cocycle extracted from the
normalized finite-coset section.  This reuses the generic cocycle theorem
rather than duplicating its associativity proof.

If two representative systems differ pointwise by lattice vectors, their
normalized differences form a `NormalizedCochain`, and their factors must be
related by `NormalizedCocycle.changeBy`.  No field of `FiniteCosetData` should
be strengthened or changed.

## 6. Boundary with `groupCohomology.H2`

The explicit M9a API remains the normative core.  M9b must not import
`groupCohomology.H2`, `ModuleCat`, a bar resolution, or a homological complex
into the dependency path of extension classification or the wallpaper
adapters.

The following may be implemented in a separate optional adapter file:

- identify `NormalizedCocycle.cocycle` with
  `groupCohomology.IsCocycle₂`;
- identify the explicit coboundary formula with
  `groupCohomology.IsCoboundary₂`;
- map `CocycleClass ρ` to mathlib's `groupCohomology.H2`; and
- compare the cyclic period theorem with mathlib's finite-cyclic even-degree
  computation.

None of these comparisons may block M9b completion.  The project does not
need to fill mathlib's missing general theorem relating `H²` to extension
classes, because M9b proves the required explicit classification directly.

## 7. Future higher-dimensional use

M9b should finish with a thin specialization to:

```text
T = Fin n → ℤ
```

or to an explicitly supplied equivalence:

```text
T ≃+ (Fin n → ℤ).
```

It should expose the fixed-action classification for a finite group with an
integral action as an input interface.  The generic cocycle and extension
theorems themselves must retain no finiteness, rank, dimension, metric, or
plane assumptions.

This abstraction is useful to a future space-group enumerator because it
provides:

- inspectable cocycle and coboundary data;
- a certified twisted extension;
- fixed-action equivalence;
- transport under compatible lattice and point-group equivalences; and
- a place to attach later finite certificates.

M9b does not implement:

- finite subgroups of `GL_n(ℤ)` or their integral-conjugacy classification;
- a computable `H²` or Smith-normal-form enumeration engine;
- normalizer actions or orbit representatives;
- affine/crystallographic realization certificates;
- a higher-dimensional Bieberbach theorem;
- a space-group catalog; or
- any three-dimensional classification.

Those require a separate roadmap and soundness/completeness statements.

## 8. Required, optional, and excluded work

### M9b must complete

- bundle `changeByMulEquiv` as a fixed-endpoint `GroupExtension.Equiv`;
- transport normalized sections and prove exact cocycle naturality;
- reconstruct every extension with a normalized section as a twisted product;
- prove the canonical twisted-product
  `extension equivalence ↔ CocycleCohomologous` theorem;
- prove the corresponding pairwise theorem for arbitrary fixed-action
  extensions;
- expose a choice-independent quotient-valued cocycle class and its
  realization theorem;
- implement compatible kernel/quotient/action transport;
- connect `TranslationPreservingIso` through a thin heterogeneous transport
  adapter;
- prove the cyclic-period comparison with the existing `shiftClass`;
- implement the quotient-valued and factor-valued `FiniteCosetData` adapters;
- retain the existing M4--M6 classification proofs unchanged; and
- add the thin free-abelian rank-`n` specialization.

### Optional extensions

- a separate adapter to mathlib's `groupCohomology.H2`;
- a named zero-cocycle equivalence with mathlib's semidirect product beyond
  the M4 regression theorem;
- an additional `wordFactor`/dihedral convenience corollary; and
- a literal quotient-type equivalence, but only if a later concrete consumer
  justifies bundling all middle-group types.

### Explicitly not part of M9b

- changing `GroupExtension`, `PlaneGroup`, `FiniteCosetData`, or
  `ShiftClassGroup`;
- changing the M9a cocycle or section conventions;
- rewriting M4--M7 in cohomological language;
- making abstract `H²` a required dependency;
- quotienting by all endpoint automorphisms or normalizer actions;
- implementing a general-purpose group-cohomology library; or
- implementing a higher-dimensional enumerator or catalog.

## 9. Recommended implementation stages

### M9b-1: fixed endpoints and reconstruction

1. Bundle coboundary coordinate changes as `GroupExtension.Equiv`.
2. Add normalized-section transport and factor/cocycle naturality.
3. Define the normal-form homomorphism and reconstruction equivalence.
4. Prove the twisted-product and arbitrary-extension pairwise classifiers.
5. Package the choice-independent cocycle class.

Suggested file:

```text
WallpaperGroups/Extensions/Classification.lean
```

### M9b-2: endpoint transport

1. Define action-compatible additive/group endpoint equivalences.
2. Transport cochains, cocycles, coboundaries, and cocycle classes.
3. Define the heterogeneous extension equivalence.
4. Add the `TranslationPreservingIso` adapter.
5. Add only thin M4 and M6 regression corollaries.

Suggested files:

```text
WallpaperGroups/Extensions/Transport.lean
WallpaperGroups/Extensions/WallpaperTransport.lean
```

### M9b-3: cyclic and finite-coset adapters

1. Define generic cyclic period evaluation.
2. Prove fixedness, coboundary/norm change, and the section-power formula.
3. Identify the specialized quotient class with M5 `shiftClass`.
4. Define the finite-coset quotient `1`-cocycle.
5. Normalize the finite-coset section and identify its lattice factor.
6. Prove representative-change/coboundary compatibility.

Suggested files:

```text
WallpaperGroups/Extensions/CyclicRestriction.lean
WallpaperGroups/Extensions/WallpaperAdapters.lean
```

### M9b-4: future-facing boundary and final review

1. Add the thin rank-`n` integral-action specialization.
2. Add the optional `H²` adapter only if it remains isolated and inexpensive.
3. Document the final generic theorem and all two-dimensional comparison
   theorems.
4. Run the full build and forbidden-placeholder checks before the M9b human
   review gate.

The stages are dependency order, not separate milestones or permission to
commit a partially reviewed final theorem.

## 10. Main risks

1. **Sign direction.**  The only accepted convention is
   `d = c.changeBy b = c + δb`, with coordinate map
   `(t, g) ↦ (t - b(g), g)`.
2. **Noncanonical sections.**  A chosen cocycle is construction data.  Only
   its `CocycleClass` is a public invariant.
3. **Endpoint confusion.**  `GroupExtension.Equiv` is correct only when kernel
   and quotient types are fixed.  Heterogeneous transport must be visibly
   separate.
4. **Universe overreach.**  A quotient of all possible middle-group types is
   unnecessary for the classification theorem.
5. **Finite-coset normalization.**  `shift 1` is only lattice-valued, so raw
   shifts cannot silently be treated as normalized.
6. **Cyclic boundary cases.**  The adapter should retain the existing
   assumption `h ^ q = 1`; it must not add exact-order or positivity hypotheses
   without need.
7. **Dependency inversion.**  The generic extension core must not import
   `Plane`, M8 topology, wallpaper models, or classification labels.
8. **Overclaiming computation.**  Arbitrary-section reconstruction is
   noncomputable.  M9b supplies a structural classifier, not a finite
   enumeration algorithm.

## 11. Human review questions

Please confirm:

1. that mathlib's fixed-endpoint `GroupExtension.Equiv` is the intended primary
   equivalence;
2. that the pairwise iff theorem plus twisted-product realization is the
   required fixed-action classification, without a quotient of all middle
   types;
3. that the quotient-valued `CocycleClass`, rather than a chosen cocycle, is
   the public invariant;
4. that heterogeneous endpoint transport is required but normalizer/orbit
   quotienting is deferred;
5. that the explicit cyclic-period theorem must identify with the existing
   M5 `shiftClass`;
6. that the two `FiniteCosetData` objects—quotient `1`-cocycle and lattice
   `2`-cocycle—are kept distinct;
7. that the optional `H²` adapter may not block M9b; and
8. that the thin rank-`n` input interface is sufficient preparation for a
   future enumerator.

Until these points are approved, M9b implementation has not started.
