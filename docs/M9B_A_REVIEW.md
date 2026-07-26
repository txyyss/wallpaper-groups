Review status: approved

# M9b-a fixed-action extension-equivalence core review

## Scope

M9b-a implements only the fixed-action, fixed-endpoint extension-equivalence
core approved in [`M9B_DESIGN_REVIEW.md`](M9B_DESIGN_REVIEW.md).  It reuses
mathlib's `GroupExtension.Equiv`; it does not define a competing notion of
extension equivalence.

This stage adds:

- coboundary coordinate changes bundled as endpoint-preserving extension
  equivalences;
- transport of normalized sections through those equivalences;
- exact naturality of section factors and extracted cocycles;
- reconstruction of an extension with a normalized section from its twisted
  product; and
- the equivalence between canonical twisted-product extension equivalence and
  `CocycleCohomologous`.

It does not implement heterogeneous kernel/quotient/action transport, an M5
`shiftClass` adapter, an abstract `H²` adapter, a quotient over all possible
middle-group types, or M9b-b.

No Version 1, M8, or M9a definition was modified.

## Source module

The implementation is in:

```text
WallpaperGroups/Extensions/Classification.lean
```

The root `WallpaperGroups.lean` imports the new module.

## Coboundary extension equivalence

M9a already supplied the computable group equivalence:

```lean
TwistedProduct.changeByMulEquiv
```

with coordinate formula:

```text
(t, g) ↦ (t - b(g), g)
```

for:

```text
c.changeBy b = c + δb.
```

M9b-a bundles its already proved endpoint equations as:

```lean
def TwistedProduct.changeByExtensionEquiv
    (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) :
    (TwistedProduct.toGroupExtension c).Equiv
      (TwistedProduct.toGroupExtension (c.changeBy b))
```

The kernel and quotient endpoint maps are identities because
`GroupExtension.Equiv` records:

```text
equiv ∘ source.inl = target.inl
target.rightHom ∘ equiv = source.rightHom.
```

No inverse is chosen: the existing `changeByMulEquiv` is used directly.

## Normalized-section transport and naturality

A normalized section is transported through an endpoint-preserving extension
equivalence by:

```lean
def NormalizedSection.equivComp
    (s : NormalizedSection S)
    (e : S.Equiv S') :
    NormalizedSection S'
```

Its pointwise behavior is:

```lean
theorem NormalizedSection.equivComp_apply :
  s.equivComp e h = e (s h)
```

Because the kernel endpoint is fixed, the factor is preserved exactly:

```lean
theorem NormalizedSection.factor_equivComp :
  factor (s.equivComp e) g h = factor s g h
```

For two extensions over the same explicit action `ρ`, the extracted cocycle
is also preserved exactly:

```lean
theorem NormalizedSection.toCocycle_equivComp
    (X : ExtensionOverAction (E := E) ρ)
    (Y : ExtensionOverAction (E := E') ρ)
    (s : NormalizedSection X.toGroupExtension)
    (e : X.toGroupExtension.Equiv Y.toGroupExtension) :
    (s.equivComp e).toCocycle Y = s.toCocycle X
```

This stage proves only fixed-endpoint naturality.  Heterogeneous action and
endpoint transport remains M9b-b work.

## Twisted-product reconstruction

For:

```lean
X : ExtensionOverAction (E := E) ρ
s : NormalizedSection X.toGroupExtension
```

the normal-form homomorphism is:

```lean
noncomputable def NormalizedSection.normalFormHom :
    TwistedProduct (s.toCocycle X) →* E
```

with formula:

```text
(t, h) ↦ X.inl (Multiplicative.ofAdd t) * s(h).
```

Multiplicativity uses only:

- the twisted-product multiplication law;
- `NormalizedSection.conjugation_inl`; and
- `NormalizedSection.inl_factor`.

The endpoint equations are exported as:

```lean
NormalizedSection.normalFormHom_inl
NormalizedSection.rightHom_normalFormHom
```

The reconstruction is then:

```lean
noncomputable def NormalizedSection.twistedProductExtensionEquiv
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension) :
    (TwistedProduct.toGroupExtension (s.toCocycle X)).Equiv
      X.toGroupExtension
```

It is built with `GroupExtension.Equiv.ofMonoidHom`.  Mathlib derives the
inverse from exactness, so M9b-a does not choose or expose another inverse
coordinate function.

The section is an explicit argument.  Therefore the extracted cocycle is not
presented as a canonical invariant of the extension; changing the section is
still controlled by M9a's proved coboundary theorem.

## Fixed-action cocycle classification core

The main M9b-a theorem is:

```lean
theorem TwistedProduct.extensionEquiv_iff_cocycleCohomologous
    (c d : NormalizedCocycle ρ) :
    Nonempty
        ((TwistedProduct.toGroupExtension c).Equiv
          (TwistedProduct.toGroupExtension d)) ↔
      CocycleCohomologous c d
```

For the forward direction, the canonical section of `c` is transported through
the supplied extension equivalence and compared with the canonical section of
`d`.  Exact cocycle naturality followed by
`NormalizedSection.toCocycle_change` gives:

```text
d = c.changeBy b.
```

For the reverse direction, the witness `d = c.changeBy b` is sent directly to
`TwistedProduct.changeByExtensionEquiv c b`.

This theorem classifies the canonical twisted products at fixed action and
fixed endpoints.  Packaging the analogous pairwise theorem for arbitrary
extensions and a quotient-valued extension class remains later M9b work; no
large quotient of all middle-group types is introduced here.

## Complete list of new declarations

```text
TwistedProduct.changeByExtensionEquiv
NormalizedSection.equivComp
NormalizedSection.equivComp_apply
NormalizedSection.factor_equivComp
NormalizedSection.toCocycle_equivComp
NormalizedSection.normalFormHom
NormalizedSection.normalFormHom_apply
NormalizedSection.normalFormHom_inl
NormalizedSection.rightHom_normalFormHom
NormalizedSection.twistedProductExtensionEquiv
NormalizedSection.twistedProductExtensionEquiv_apply
TwistedProduct.extensionEquiv_iff_cocycleCohomologous
```

## Dependency and choice boundary

- The core remains dimension-independent.
- There are no finiteness, freeness, rank, metric, plane, or wallpaper-label
  assumptions.
- The implementation imports no `groupCohomology.H2`, `ModuleCat`, or
  homological complex.
- `GroupExtension.Equiv` is the only fixed-endpoint equivalence structure.
- Reconstruction is noncomputable only because arbitrary extension
  coordinates are recovered from exactness.
- A section remains explicit construction data and is not a public invariant.
- No Version 1, M8, or M9a declaration is changed.

## Deferred M9b work

M9b-b and later M9b stages still need:

1. the arbitrary-extension pairwise classifier and quotient-valued cocycle
   class;
2. heterogeneous kernel, quotient, and action transport;
3. the `TranslationPreservingIso` transport adapter;
4. the cyclic-period comparison with M5 `shiftClass`;
5. the quotient-valued and lattice-factor `FiniteCosetData` adapters;
6. the thin free-abelian rank-`n` specialization; and
7. the final generic M9b theorem and its human review.

An abstract mathlib `H²` comparison remains optional and may not block this
work.

## Human review checklist

Please review:

1. whether `GroupExtension.Equiv` records exactly the intended
   endpoint-preserving relation;
2. whether the sign
   `d = c.changeBy b` with `(t, g) ↦ (t - b(g), g)` is correct;
3. whether transported section factors and cocycles should be exactly equal,
   rather than merely cohomologous;
4. whether reconstruction has the intended direction and normal form;
5. whether the two reconstruction endpoint equations are sufficient;
6. whether the `Nonempty GroupExtension.Equiv ↔ CocycleCohomologous` theorem
   has the intended fixed-action strength; and
7. whether the deferred list correctly prevents M9b-a from claiming the full
   M9b classification.

## Validation

- `lake build WallpaperGroups.Extensions.Classification` succeeds with 1104
  jobs.
- The root `WallpaperGroups.lean` file compiles with the new import.
- `lake build` succeeds with 2888 jobs.
- `git diff --check` succeeds.
- The project Lean-source scan finds no `sorry`, `admit`, `axiom`, or
  `unsafe`.
- No toolchain, dependency, Version 1, M8, or M9a source file is modified.
