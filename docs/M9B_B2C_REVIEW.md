Review status: approved

# M9b-b2c heterogeneous extension classifier review

## Scope and staging

M9b-b2c combines the three approved layers:

```text
M9b-b1  fixed-action extension classification
M9b-b2a action, cochain, and cocycle transport
M9b-b2b extension endpoint transport
```

This snapshot implements:

- a thin heterogeneous extension equivalence over the existing
  `GroupExtension.Equiv`;
- its identity, symmetry, and composition interfaces;
- normalized-section and twisted-product transport; and
- the arbitrary-extension heterogeneous cocycle classifier.

The approved M9b-b2 design originally grouped a
`TranslationPreservingIso` consumer with this stage.  The project owner's
current implementation request scopes this snapshot to the generic
classifier; that adapter and all other project-specific adapters remain later
work.  This is an implementation-stage refinement, not a change to the
approved generic classifier.

No Version 1, M8, M9a, M9b-a, M9b-b1, M9b-b2a, or M9b-b2b declaration was
modified.

## Source and dependency boundary

The implementation is:

```text
WallpaperGroups/Extensions/HeterogeneousClassification.lean
```

Its project imports are:

```text
WallpaperGroups.Extensions.Classification
WallpaperGroups.Extensions.EndpointTransport
```

The root `WallpaperGroups.lean` imports the module.  The new file imports no
plane geometry, lattices, wallpaper labels, finite-coset models, shift
classes, or homological group cohomology.

## Thin heterogeneous equivalence

The definition is an abbreviation:

```lean
abbrev ExtensionOverAction.EquivAlong
    (X : ExtensionOverAction (E := E) ρ)
    (a : AdditiveAction.Equiv ρ ρ')
    (Y : ExtensionOverAction (E := E') ρ') :=
  (X.transport a).toGroupExtension.Equiv Y.toGroupExtension
```

Thus `EquivAlong` contains no new equivalence fields.  It first transports the
source extension to the target kernel, quotient, and action, then uses
mathlib's existing endpoint-preserving `GroupExtension.Equiv`.

For:

```text
e : X.EquivAlong a Y
```

the two heterogeneous endpoint squares are:

```text
e (X.inl (Multiplicative.ofAdd t)) =
  Y.inl (Multiplicative.ofAdd (a.kernelEquiv t))

Y.rightHom (e x) =
  a.quotientEquiv (X.rightHom x).
```

They are exported as:

```text
ExtensionOverAction.EquivAlong.map_inl
ExtensionOverAction.EquivAlong.rightHom_map
```

Notice the two compatible directions:

- `ExtensionOverAction.transport` internally uses `kernelEquiv.symm` when
  interpreting a target kernel coordinate in the source extension;
- the heterogeneous square above maps an original source coordinate forward
  by `kernelEquiv`.

## Identity, symmetry, and composition

For the identity action equivalence, the implementation supplies conversions
in both directions:

```text
ExtensionOverAction.EquivAlong.ofRefl
ExtensionOverAction.EquivAlong.toRefl
```

and bundles them as:

```lean
def ExtensionOverAction.EquivAlong.reflEquiv :
    X.EquivAlong (AdditiveAction.Equiv.refl ρ) Y ≃
      X.toGroupExtension.Equiv Y.toGroupExtension
```

The exact proposition-level specialization is:

```lean
theorem ExtensionOverAction.EquivAlong.equivAlong_refl_iff :
    Nonempty
        (X.EquivAlong (AdditiveAction.Equiv.refl ρ) Y) ↔
      Nonempty
        (X.toGroupExtension.Equiv Y.toGroupExtension)
```

Symmetry reverses both the middle-group equivalence and action equivalence:

```lean
def ExtensionOverAction.EquivAlong.symm
    (e : X.EquivAlong a Y) :
    Y.EquivAlong a.symm X
```

Composition uses source-to-target action composition:

```lean
def ExtensionOverAction.EquivAlong.trans
    (e : X.EquivAlong a Y)
    (e' : Y.EquivAlong a' Z) :
    X.EquivAlong (a.trans a') Z
```

Both constructions remain values of the existing `GroupExtension.Equiv`;
they prove the transported endpoint squares rather than introducing a parallel
record.

## Normalized-section transport

For:

```text
s : NormalizedSection X.toGroupExtension
a : AdditiveAction.Equiv ρ ρ'
```

the definition is:

```lean
def NormalizedSection.transport
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (a : AdditiveAction.Equiv ρ ρ') :
    NormalizedSection (X.transport a).toGroupExtension
```

with pointwise formula:

```text
(s.transport X a)(h') =
  s (a.quotientEquiv.symm h').
```

Precomposition by `quotientEquiv.symm` is necessary because the transported
section is a function on the target quotient.  Its factor satisfies the exact
forward-kernel formula:

```text
factor (s.transport X a) g' h' =
  a.kernelEquiv
    (factor s
      (a.quotientEquiv.symm g')
      (a.quotientEquiv.symm h')).
```

Consequently cocycle extraction commutes exactly with transport:

```lean
theorem NormalizedSection.toCocycle_transport :
    (s.transport X a).toCocycle (X.transport a) =
      (s.toCocycle X).transport a
```

After an `EquivAlong` witness, existing fixed-endpoint section transport gives:

```lean
theorem NormalizedSection.toCocycle_equivAlong :
    ((s.transport X a).equivComp e).toCocycle Y =
      (s.toCocycle X).transport a
```

The factor proof uses its proved characterization under the injective kernel
map.  It does not unfold or expose the noncanonical `Function.invFun` used by
the general factor construction.

## Twisted-product transport

For `c : NormalizedCocycle ρ`, the computable coordinate equivalence is:

```lean
def TwistedProduct.transportMulEquiv
    (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    TwistedProduct c ≃*
      TwistedProduct (c.transport a)
```

Its map is exactly:

```text
(t, h) ↦ (a.kernelEquiv t, a.quotientEquiv h).
```

Multiplicativity follows from:

- additive naturality of `kernelEquiv`;
- `a.intertwines` for the action term; and
- the pointwise formula for `NormalizedCocycle.transport`.

The coordinate formulas are:

```text
TwistedProduct.transportMulEquiv_left
TwistedProduct.transportMulEquiv_right
```

The equivalence is bundled as the canonical heterogeneous extension witness:

```lean
def TwistedProduct.transportExtensionEquivAlong
    (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    (TwistedProduct.toExtensionOverAction c).EquivAlong a
      (TwistedProduct.toExtensionOverAction (c.transport a))
```

This supplies a concrete regression test for both endpoint-square directions.

## Heterogeneous classifier

The final theorem has the complete type:

```lean
theorem ExtensionOverAction.equivAlong_iff_cocycleCohomologous
    (X : ExtensionOverAction (E := E) ρ)
    (Y : ExtensionOverAction (E := E') ρ')
    (a : AdditiveAction.Equiv ρ ρ')
    (s : NormalizedSection X.toGroupExtension)
    (t : NormalizedSection Y.toGroupExtension) :
    Nonempty (X.EquivAlong a Y) ↔
      CocycleCohomologous
        ((s.toCocycle X).transport a)
        (t.toCocycle Y)
```

Only the source cocycle is transported, because both cocycles must be compared
over the target action `ρ'`.

The proof is the intended reduction:

1. transport `X` along `a`;
2. transport `s` by precomposition with `a.quotientEquiv.symm`;
3. rewrite its extracted cocycle using exact naturality; and
4. apply the approved M9b-b1 fixed-action theorem
   `ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous`.

The theorem quantifies over arbitrary supplied normalized sections.  It
therefore does not turn a section choice into a public invariant and does not
construct a type containing all possible middle groups.

## Declaration inventory and dependency flow

```text
ExtensionOverAction.EquivAlong
ExtensionOverAction.EquivAlong.map_inl
ExtensionOverAction.EquivAlong.rightHom_map
ExtensionOverAction.EquivAlong.ofRefl
ExtensionOverAction.EquivAlong.toRefl
ExtensionOverAction.EquivAlong.reflEquiv
ExtensionOverAction.EquivAlong.equivAlong_refl_iff
ExtensionOverAction.EquivAlong.symm
ExtensionOverAction.EquivAlong.trans

NormalizedSection.transport
NormalizedSection.transport_apply
NormalizedSection.factor_transport
NormalizedSection.toCocycle_transport
NormalizedSection.toCocycle_equivAlong

TwistedProduct.transportMulEquiv
TwistedProduct.transportMulEquiv_left
TwistedProduct.transportMulEquiv_right
TwistedProduct.transportExtensionEquivAlong

ExtensionOverAction.equivAlong_iff_cocycleCohomologous
```

The dependency flow is:

```text
action transport + endpoint transport
  → EquivAlong and section transport
  → exact section-cocycle naturality
  → M9b-b1 fixed-action classifier
  → heterogeneous classifier

cocycle transport + action intertwining
  → twisted-product coordinate equivalence
  → canonical twisted-product EquivAlong witness
```

## Deferred M9 work

This snapshot does not implement:

- a `TranslationPreservingIso` action/extension adapter;
- an M8 geometric convenience adapter;
- the M5 `ShiftClass` comparison;
- a `FiniteCosetData` adapter;
- a free-abelian rank-`n` specialization;
- an abstract `H²` adapter; or
- any new space-group enumeration direction.

No large quotient over middle-group types, endpoint actions, or endpoint
automorphisms is introduced.  At final M9 core approval, the project owner
designated these adapters as future extensions rather than requirements for
`m9-complete`.

## Human review checklist

Please review:

1. whether `EquivAlong` is exactly the approved transport-then-existing-
   equivalence thin layer;
2. whether the kernel and quotient endpoint squares use the correct forward
   directions;
3. whether identity specialization, symmetry, and composition match the
   action-equivalence operations;
4. whether normalized-section transport correctly precomposes with
   `quotientEquiv.symm`;
5. whether factor and extracted-cocycle transport use forward
   `kernelEquiv`;
6. whether twisted-product coordinate transport preserves multiplication and
   both extension endpoints;
7. whether the classifier transports only the source cocycle to the target
   action;
8. whether quantification over arbitrary normalized sections adequately
   preserves choice independence;
9. whether reusing the fixed-action classifier introduces no hidden
   assumption; and
10. whether the deferred adapter boundary correctly follows the current
    implementation request.

## Validation

- `lake env lean
  WallpaperGroups/Extensions/HeterogeneousClassification.lean` succeeds
  without warnings.
- `lake build
  WallpaperGroups.Extensions.HeterogeneousClassification` succeeds with 1107
  jobs.
- The root `WallpaperGroups.lean` compiles with the new import.
- The final full `lake build` succeeds with 2891 jobs.
- `git diff --check` succeeds.
- The project Lean-source scan finds no `sorry`, `admit`, `axiom`, or
  `unsafe`.
- No toolchain or dependency configuration changed.
- No protected Version 1, M8, M9a, M9b-a, M9b-b1, M9b-b2a, or M9b-b2b
  declaration changed.
