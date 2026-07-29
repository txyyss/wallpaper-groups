Review status: approved

# M9b-b2 heterogeneous extension transport design review

## 1. Scope and decision

This is a design-only snapshot.  It adds no Lean implementation and changes no
existing mathematical definition.

M9b-b1 classifies extensions only after the additive kernel `T`, quotient group
`H`, and explicit action `ρ` have been fixed.  M9b-b2 should add the transport
layer needed to compare:

```text
ρ  : AdditiveAction H  T
ρ' : AdditiveAction H' T'
```

along compatible endpoint equivalences:

```text
eT : T ≃+ T'
eH : H ≃* H'.
```

The selected architecture is:

1. bundle `eT`, `eH`, and their action-intertwining law;
2. transport explicit cochains and cocycles from `ρ` to `ρ'`;
3. transport the source extension itself to the target endpoints while
   retaining its middle group;
4. compare that transported extension with the target using mathlib's
   existing fixed-endpoint `GroupExtension.Equiv`; and
5. reuse the approved M9b-b1 classifier without reproving it.

In particular, M9b-b2 should not introduce a second fixed-endpoint extension
equivalence.  Its heterogeneous relation is an existing
`GroupExtension.Equiv` after explicit endpoint transport.

The direction convention throughout this document is source to target:

```text
(T, H, ρ) --a--> (T', H', ρ').
```

## 2. Audited support and current gap

The pinned mathlib and the current project already provide:

```text
GroupExtension
GroupExtension.Equiv
GroupExtension.Equiv.map_inl
GroupExtension.Equiv.rightHom_map
GroupExtension.Equiv.refl
GroupExtension.Equiv.symm
GroupExtension.Equiv.trans
GroupExtension.Equiv.ofMonoidHom
GroupExtension.Section.equivComp
AddEquiv.toMultiplicative
```

The project additionally provides:

```text
GroupExtension.relabelKernel
ExtensionOverAction
NormalizedSection.equivComp
NormalizedSection.toCocycle_equivComp
ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous
```

`GroupExtension.Equiv` deliberately fixes its kernel and quotient types.  The
repository has a kernel-relabeling helper, but neither the project nor the
pinned mathlib has the corresponding quotient-relabeling or combined endpoint
transport helper.  That is the only foundational API gap identified by this
audit.

No general group-cohomology API is needed for this layer.

## 3. Compatible action equivalence

### 3.1 Proposed structure

The central new datum should have the following public shape:

```lean
structure AdditiveAction.Equiv
    {H T H' T' : Type*}
    [Group H] [AddCommGroup T]
    [Group H'] [AddCommGroup T']
    (ρ : AdditiveAction H T) (ρ' : AdditiveAction H' T') where
  kernelEquiv : T ≃+ T'
  quotientEquiv : H ≃* H'
  intertwines :
    ∀ (h : H) (t : T),
      kernelEquiv (ρ.apply h t) =
        ρ'.apply (quotientEquiv h) (kernelEquiv t)
```

The field names may be shortened during implementation only if the resulting
API remains equally explicit.  The mathematical direction must not change.

The action law is exactly:

```text
eT (ρ(h)(t)) = ρ'(eH(h))(eT(t)).
```

It is not enough to carry unrelated equivalences of `T` and `H`.  Without this
law, transported cocycles do not satisfy the target cocycle identity and
transported extensions need not induce `ρ'`.

### 3.2 Required coherence

M9b-b2 should provide:

```text
AdditiveAction.Equiv.refl
AdditiveAction.Equiv.symm
AdditiveAction.Equiv.trans
```

with the expected source-to-target directions.  These are required for
round-trip and composition statements; they are not an endpoint-automorphism
orbit construction.

## 4. Cochain and cocycle transport

### 4.1 Pointwise definitions

For:

```text
a : AdditiveAction.Equiv ρ ρ'
```

transport a normalized cochain by:

```text
(b.transport a)(h') =
  a.kernelEquiv (b (a.quotientEquiv.symm h')).
```

The proposed type is:

```lean
def NormalizedCochain.transport
    (a : AdditiveAction.Equiv ρ ρ')
    (b : NormalizedCochain H T) :
    NormalizedCochain H' T'
```

Transport a normalized cocycle by:

```text
(c.transport a)(g', h') =
  a.kernelEquiv
    (c (a.quotientEquiv.symm g')
       (a.quotientEquiv.symm h')).
```

The proposed type is:

```lean
def NormalizedCocycle.transport
    (a : AdditiveAction.Equiv ρ ρ')
    (c : NormalizedCocycle ρ) :
    NormalizedCocycle ρ'
```

The inverse occurrences of `eH` are essential: the transported objects are
functions on the target quotient group.

### 4.2 Exact naturality

The following are required equalities, not merely cohomology statements:

```lean
(b.coboundary ρ).transport a =
  (b.transport a).coboundary ρ'
```

```lean
(c.changeBy b).transport a =
  (c.transport a).changeBy (b.transport a)
```

They verify both the action-intertwining direction and the accepted
coboundary sign:

```text
d = c.changeBy b = c + δb.
```

Transport must also satisfy identity, composition, and inverse round trips:

```text
c.transport (AdditiveAction.Equiv.refl ρ) = c
(c.transport a).transport a' = c.transport (a.trans a')
(c.transport a).transport a.symm = c
```

and the analogous statements for normalized cochains.

### 4.3 `CocycleCohomologous` naturality

The relation-level result should be an iff:

```lean
theorem CocycleCohomologous.transport_iff
    (a : AdditiveAction.Equiv ρ ρ')
    (c d : NormalizedCocycle ρ) :
    CocycleCohomologous c d ↔
      CocycleCohomologous (c.transport a) (d.transport a)
```

The forward direction transports the witnessing cochain.  The reverse
direction transports a target witness through `a.symm` and uses the round-trip
equalities.

This theorem is the required naturality result.  It is sufficient to induce an
equivalence of explicit cocycle-class quotients if such a short alias is added
later.  M9b-b2 need not create a quotient over all possible actions or endpoint
types.

## 5. Endpoint transport for group extensions

### 5.1 Quotient relabeling

The existing:

```lean
GroupExtension.relabelKernel
```

changes only the kernel presentation.  Add the symmetric helper:

```lean
def GroupExtension.relabelQuotient
    (S : GroupExtension N E H)
    (eH : H ≃* H') :
    GroupExtension N E H'
```

with:

```text
inl       = S.inl
rightHom  = eH ∘ S.rightHom.
```

Injectivity of `eH` keeps the same kernel, and surjectivity of `eH` preserves
surjectivity of the quotient projection.

The combined source-to-target transport should then be:

```lean
def GroupExtension.transportEndpoints
    (S : GroupExtension N E H)
    (eN : N ≃* N')
    (eH : H ≃* H') :
    GroupExtension N' E H' :=
  (S.relabelKernel eN.symm).relabelQuotient eH
```

The inverse on `eN` is forced by the existing `relabelKernel` convention:
the new kernel inclusion sends `n'` to `S.inl (eN.symm n')`.

### 5.2 Transport of `ExtensionOverAction`

For:

```text
a : AdditiveAction.Equiv ρ ρ'
X : ExtensionOverAction (E := E) ρ
```

define:

```lean
def ExtensionOverAction.transport
    (a : AdditiveAction.Equiv ρ ρ')
    (X : ExtensionOverAction (E := E) ρ) :
    ExtensionOverAction (E := E) ρ'
```

using:

```text
eN = AddEquiv.toMultiplicative a.kernelEquiv
eH = a.quotientEquiv.
```

It retains the middle group `E` and has the concrete endpoint maps:

```text
inl'(t')       = X.inl(a.kernelEquiv.symm(t'))
rightHom'(x)   = a.quotientEquiv(X.rightHom(x)).
```

Here the first formula suppresses only the `Multiplicative.ofAdd/toAdd` tags.
The proof that this extension induces `ρ'` is exactly the
`a.intertwines` field applied after `a.kernelEquiv.symm`.

No section, basis, or other noncanonical choice is involved.

## 6. Heterogeneous extension equivalence

### 6.1 Thin definition over existing `GroupExtension.Equiv`

For source and target extensions:

```text
X : ExtensionOverAction (E := E)  ρ
Y : ExtensionOverAction (E := E') ρ'
```

and `a : AdditiveAction.Equiv ρ ρ'`, define:

```lean
abbrev ExtensionOverAction.EquivAlong
    (a : AdditiveAction.Equiv ρ ρ')
    (X : ExtensionOverAction (E := E) ρ)
    (Y : ExtensionOverAction (E := E') ρ') :=
  (X.transport a).toGroupExtension.Equiv Y.toGroupExtension
```

Thus the heterogeneous relation is literally a fixed-endpoint
`GroupExtension.Equiv` after the source endpoints are transported.

If `e : X.EquivAlong a Y`, its underlying middle-group equivalence
`eE : E ≃* E'` satisfies:

```text
eE (X.inl(t)) =
  Y.inl(a.kernelEquiv(t))
```

and:

```text
Y.rightHom(eE(x)) =
  a.quotientEquiv(X.rightHom(x)).
```

These are the required heterogeneous endpoint squares.  They should be
exported as named simp lemmas derived from:

```text
GroupExtension.Equiv.map_inl
GroupExtension.Equiv.rightHom_map.
```

No parallel record duplicating those two fixed-endpoint fields is needed.

### 6.2 Relationship with the fixed-endpoint layer

For the identity action equivalence, M9b-b2 should construct a canonical
identity-middle-group equivalence between `X.transport refl` and `X`.  It
should then prove that:

```text
Nonempty (X.EquivAlong (AdditiveAction.Equiv.refl ρ) Y)
```

is logically equivalent to:

```text
Nonempty (X.toGroupExtension.Equiv Y.toGroupExtension).
```

Judgmental equality of the transported structure is not required.  The
existing M9b-a/M9b-b1 relation remains the primary fixed-endpoint relation.

Symmetry and composition along `a.symm` and `a.trans a'` should be supplied
through the endpoint-transport coherence equivalences and
`GroupExtension.Equiv.symm/trans`.

## 7. Sections, twisted products, and the heterogeneous classifier

### 7.1 Transported normalized sections

Given:

```text
s : NormalizedSection X.toGroupExtension
```

define a normalized section of `X.transport a` by:

```text
(s.transport a)(h') = s(a.quotientEquiv.symm h').
```

The middle group has not changed.  The quotient projection has changed, so
precomposition by `eH.symm` makes this a section of the transported extension.

Its factor and cocycle should satisfy exact formulas:

```text
factor(s.transport a)(g', h') =
  a.kernelEquiv
    (factor(s)(a.quotientEquiv.symm g',
               a.quotientEquiv.symm h'))
```

and:

```lean
(s.transport a).toCocycle (X.transport a) =
  (s.toCocycle X).transport a
```

After applying `NormalizedSection.equivComp` to an
`e : X.EquivAlong a Y`, the approved fixed-endpoint naturality theorem applies
unchanged.

### 7.2 Twisted-product transport

For `c : NormalizedCocycle ρ`, M9b-b2 should provide the computable
middle-group map:

```text
(t, h) ↦ (a.kernelEquiv(t), a.quotientEquiv(h))
```

as an equivalence from `TwistedProduct c` to
`TwistedProduct (c.transport a)`.  Its multiplication proof is precisely the
cocycle transport formula and the action-intertwining law.

Bundling its endpoint squares gives a canonical `EquivAlong` witness for the
two twisted-product extensions.  This is both a useful consumer and a
regression check for the direction conventions.

### 7.3 Final M9b-b2 theorem

For arbitrary supplied normalized sections:

```lean
theorem ExtensionOverAction.equivAlong_iff_cocycleCohomologous
    (a : AdditiveAction.Equiv ρ ρ')
    (X : ExtensionOverAction (E := E) ρ)
    (Y : ExtensionOverAction (E := E') ρ')
    (s : NormalizedSection X.toGroupExtension)
    (t : NormalizedSection Y.toGroupExtension) :
    Nonempty (X.EquivAlong a Y) ↔
      CocycleCohomologous
        ((s.toCocycle X).transport a)
        (t.toCocycle Y)
```

The proof route is deliberately short:

1. transport `X` and `s` along `a`;
2. rewrite the transported section cocycle by exact naturality; and
3. apply the approved
   `ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous`.

The statement quantifies over arbitrary sections.  It therefore preserves the
M9b-b1 choice-independence boundary.

## 8. Connections to existing project code

### 8.1 `TranslationPreservingIso`: part of M9b-b2

This is the required first project consumer of the generic transport layer.
For:

```text
e : TranslationPreservingIso G H
```

the existing code already supplies all data:

```text
e.translationVectorEquiv
e.pointGroupEquiv
e.toMulEquiv
e.translationVector_pointAction
e.map_translationElement
e.pointGroupEquiv_pointProjection
```

Therefore M9b-b2 should define a thin action equivalence:

```text
pointActionHom G.carrier
  ≃
pointActionHom H.carrier
```

with:

```text
eT = e.translationVectorEquiv
eH = e.pointGroupEquiv.
```

`translationVector_pointAction` is exactly the required intertwining law.
The middle-group equivalence and the two endpoint-square proofs then give:

```text
EuclideanMotion.pointGroupExtensionOverAction G.carrier
  ≃[eT,eH]
EuclideanMotion.pointGroupExtensionOverAction H.carrier.
```

This adapter should use the full translation-vector groups, not chosen
`RankTwoLattice` bases.  It belongs in a plane-specific adapter module such as:

```text
WallpaperGroups/Extensions/WallpaperTransport.lean
```

The dimension-independent transport core must not import `PlaneGroup`.

### 8.2 M8 geometric adapter: deferred convenience layer

M8 introduces no new extension object.  A geometric group is converted by:

```text
GeometricWallpaperGroup.toPlaneGroup
```

without changing its carrier.  A concrete geometric motion-type isomorphism
can already be converted to a `TranslationPreservingIso` through the M8a/M8c
adapters and then use the M9b-b2 wallpaper adapter.

No M8 topology, proper-discontinuity, cocompactness, or recovered-basis data
belongs in the generic transport file.  A named geometric convenience
corollary is optional later adapter work and is not required for M9b-b2.

### 8.3 M5 `ShiftClass`: later cyclic adapter

The existing M5 API already contains transport patterns:

```text
shiftClassEquivOfIntertwining
shiftClassEquiv
shiftClass_natural
finiteNormHom_natural_of_intertwining.
```

These support the selected `eT/eH/intertwining` design.  However, proving that
the cyclic period of a transported cocycle is the existing quotient-valued
`shiftClass` requires the separate cyclic-restriction mathematics specified
by the M9b roadmap.

M9b-b2 must not implement that period theorem or modify `ShiftClassGroup`.

### 8.4 `FiniteCosetData`: later wallpaper adapter

`FiniteCosetData` stores:

```text
shift : P → Plane
shift_one_mem
cocycle_mem.
```

Its raw `shift` is not normalized: only `shift 1 ∈ lattice` is known.  It also
uses `P` rather than a point-group subtype as its quotient endpoint.  The later
adapter must first bundle the induced endpoint equivalence and normalize the
section before comparing its factor with the generic cocycle.

That work also has to keep distinct:

1. the quotient-valued `1`-cocycle represented by `shift`; and
2. the lattice-valued `2`-cocycle represented by its defect.

None of this belongs in M9b-b2.  The generic transport API should make the
later endpoint comparison possible without importing the large model file.

## 9. M9b-b2 required, deferred, and excluded work

### Required in M9b-b2

- compatible additive-action equivalences with identity, inverse, and
  composition;
- cochain and cocycle transport with exact pointwise formulas;
- transport of coboundaries and `changeBy`;
- iff naturality of `CocycleCohomologous`;
- quotient and combined endpoint relabeling for `GroupExtension`;
- transport of `ExtensionOverAction`;
- the thin `EquivAlong` relation over existing `GroupExtension.Equiv`;
- normalized-section and twisted-product transport;
- the heterogeneous arbitrary-extension classifier; and
- the `TranslationPreservingIso` action/extension adapter in a separate
  plane-specific module.

### Deferred to later M9b adapters

- geometric M8 convenience corollaries;
- cyclic period and M5 `shiftClass` comparison;
- `FiniteCosetData` quotient and factor adapters;
- M4/M6 named regression corollaries not needed by transport;
- the thin free-abelian rank-`n` input specialization; and
- any optional comparison with mathlib `H²`.

### Explicitly excluded

- changing `GroupExtension`, `ExtensionOverAction`, `PlaneGroup`,
  `TranslationPreservingIso`, `ShiftClassGroup`, or `FiniteCosetData`;
- changing the M9a cocycle, coboundary, or section convention;
- rewriting Version 1 or M8 classification proofs;
- a quotient of all middle-group types or all actions;
- quotienting by endpoint automorphism or normalizer orbits;
- importing `groupCohomology.H2`, `ModuleCat`, or homological complexes;
- implementing a space-group enumerator; and
- using a chosen basis or section as a public invariant.

## 10. Recommended implementation stages

### M9b-b2-a: action and cocycle transport

1. Add `AdditiveAction.Equiv` and its coherence operations.
2. Add normalized cochain and cocycle transport.
3. Prove coboundary, `changeBy`, and `CocycleCohomologous` naturality.
4. Verify identity, composition, and inverse round trips.

Suggested generic file:

```text
WallpaperGroups/Extensions/Transport.lean
```

### M9b-b2-b: extension transport

1. Add quotient and combined endpoint relabeling.
2. Construct `ExtensionOverAction.transport`.
3. Define `EquivAlong` as a fixed-endpoint equivalence after transport.
4. Transport normalized sections and twisted products.
5. Prove both endpoint-square lemmas and identity/composition coherence.

### M9b-b2-c: classifier and wallpaper consumer

1. Derive the heterogeneous pairwise classifier from M9b-b1.
2. Add the `TranslationPreservingIso` action equivalence.
3. Add its point-group-extension `EquivAlong` witness.
4. Run the focused and full build and forbidden-placeholder checks.
5. Stop at the M9b-b2 human-review gate before cyclic or finite-coset
   adapters.

These are implementation subphases, not permission to weaken the final
M9b-b2 theorem.

## 11. Risks and proof obligations

1. **Direction errors.**  All transport is source to target.  Cochains and
   cocycles precompose with `eH.symm`; endpoint projections postcompose with
   `eH`; the transported kernel inclusion uses `eT.symm`.
2. **Action mismatch.**  An extension may be relabeled only through an
   action-compatible pair.  Independent `eT/eH` values are insufficient.
3. **False fixed-endpoint equality.**  `X.transport refl` need not be
   judgmentally equal to `X`; a canonical fixed-endpoint equivalence is
   sufficient.
4. **Section naturality.**  A heterogeneous section is not obtained only by
   applying the middle equivalence.  Its quotient argument must also be
   precomposed with `eH.symm`.
5. **Dependent quotient data.**  Later M5 adapters contain proof parameters
   such as `h ^ q = 1`; they should use proved transport rather than expect
   judgmental equality.
6. **Dependency inversion.**  `Transport.lean` must remain independent of
   plane geometry.  Only `WallpaperTransport.lean` may import the
   translation-preserving plane-group API.
7. **Universe overreach.**  The pairwise theorem does not require a type
   containing every possible middle group.
8. **Overclaiming computation.**  Endpoint and cocycle transport are
   computable, but arbitrary-extension reconstruction remains noncomputable
   for the same reason as M9b-a.

## 12. Human review questions

Please confirm:

1. that action equivalence should consist exactly of `eT`, `eH`, and the
   displayed intertwining law;
2. that source-to-target is the accepted direction convention;
3. that endpoint transport followed by mathlib `GroupExtension.Equiv` is
   preferable to a parallel heterogeneous record;
4. that the displayed cochain, cocycle, coboundary, and heterogeneous
   classifier formulas have the intended directions;
5. that `TranslationPreservingIso` is the one required project adapter in
   M9b-b2;
6. that M8 convenience, M5 cyclic restriction, and `FiniteCosetData`
   interpretation remain later adapter work;
7. that identity endpoint transport needs equivalence, not judgmental
   equality; and
8. that endpoint-automorphism orbit quotients and abstract `H²` remain outside
   this stage.

The project owner approved this design before M9b-b2a implementation began.
The endpoint-transport and heterogeneous-classifier work in M9b-b2b and
M9b-b2c remains governed by the boundaries above.
