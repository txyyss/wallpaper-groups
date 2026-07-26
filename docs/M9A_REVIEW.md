Review status: approved

# M9a explicit cocycle-extension core review

## Scope

M9a adds a dimension-independent, explicit API for abelian-kernel group extensions.  It reuses
mathlib's `GroupExtension` as the short-exact-sequence foundation and does not import
`groupCohomology.H2`, `ModuleCat`, a bar resolution, or a homological complex.

The implementation follows the project owner's M9a task after approval of
[`M9_DESIGN_REVIEW.md`](M9_DESIGN_REVIEW.md).  That task places the explicit cocycle and twisted
product core in M9a.  Endpoint-preserving extension classification, arbitrary-extension
reconstruction, and the M5 finite-coset/`shiftClass` adapters remain later work; no M9b theorem is
claimed here.

No Version 1 or M8 definition or classification proof was modified.

## New source modules

- `WallpaperGroups/Extensions/Action.lean`
- `WallpaperGroups/Extensions/NormalizedCocycle.lean`
- `WallpaperGroups/Extensions/TwistedProduct.lean`
- `WallpaperGroups/Extensions/Section.lean`
- `WallpaperGroups/Extensions/PointGroup.lean`
- `WallpaperGroups/Extensions/DihedralFactor.lean`

The root `WallpaperGroups.lean` imports these modules.

## Explicit action and extension wrapper

The public action datum is:

```lean
abbrev AdditiveAction (H T : Type*) [Group H] [AddCommGroup T] :=
  H →* Multiplicative (AddAut T)
```

It is evaluated by:

```lean
def AdditiveAction.apply
    (ρ : AdditiveAction H T) (h : H) (t : T) : T
```

The wrapper relating a prescribed action to an existing short exact sequence is:

```lean
structure ExtensionOverAction
    (ρ : AdditiveAction H T) where
  toGroupExtension : GroupExtension (Multiplicative T) E H
  conjugation_inl :
    ∀ (e : E) (t : T),
      toGroupExtension.inl
          (Multiplicative.ofAdd
            (ρ.apply (toGroupExtension.rightHom e) t)) =
        e * toGroupExtension.inl (Multiplicative.ofAdd t) * e⁻¹
```

Thus the middle-group conjugation action is not incorrectly treated as quotient-valued without a
compatibility proof.  `WallpaperGroups.GroupExtension.relabelKernel` reparameterizes only the
left endpoint of an existing extension along a `MulEquiv`; it does not reconstruct the short
exact sequence.

## Normalized cocycles and coboundaries

The main definition is:

```lean
structure NormalizedCocycle (ρ : AdditiveAction H T) where
  toFun : H → H → T
  one_left : ∀ h, toFun 1 h = 0
  one_right : ∀ g, toFun g 1 = 0
  cocycle :
    ∀ g h k,
      toFun g h + toFun (g * h) k =
        ρ.apply g (toFun h k) + toFun g (h * k)
```

A normalized `1`-cochain is:

```lean
structure NormalizedCochain (H T : Type*) [Group H] [AddCommGroup T] where
  toFun : H → T
  map_one : toFun 1 = 0
```

Its explicit coboundary is:

```lean
def NormalizedCochain.coboundary
    (ρ : AdditiveAction H T) (b : NormalizedCochain H T) :
    NormalizedCocycle ρ
```

with pointwise value:

```text
δb(g,h) = b(g) + ρ(g)(b(h)) - b(gh).
```

`NormalizedCocycle.changeBy c b` is `c + δb`.  The relation

```lean
def CocycleCohomologous (c d : NormalizedCocycle ρ) : Prop :=
  ∃ b : NormalizedCochain H T, d = c.changeBy b
```

is proved reflexive, symmetric, and transitive and is exposed as
`CocycleCohomologous.setoid`.

## Twisted product and associativity

For `c : NormalizedCocycle ρ`:

```lean
structure TwistedProduct (c : NormalizedCocycle ρ) where
  left : T
  right : H
```

has multiplication and inverse:

```text
(t,g) * (u,h) =
  (t + ρ(g)(u) + c(g,h), gh)

(t,g)⁻¹ =
  (-ρ(g⁻¹)(t) - c(g⁻¹,g), g⁻¹).
```

The `Group` instance proves associativity directly from `c.cocycle`; the exported theorem
`TwistedProduct.associative` records the resulting multiplication law.

The following declarations construct and validate the canonical extension:

```lean
TwistedProduct.inl
TwistedProduct.rightHom
TwistedProduct.toGroupExtension
TwistedProduct.toExtensionOverAction
TwistedProduct.mul_inl
```

The kernel is `Multiplicative T`, and the quotient is exactly `H`.  Conjugating a kernel element
acts by `ρ`.

For a cochain `b`, the coordinate map:

```text
(t,g) ↦ (t - b(g), g)
```

is implemented as:

```lean
TwistedProduct.changeByMulEquiv c b :
  TwistedProduct c ≃* TwistedProduct (c.changeBy b)
```

Theorems `changeByMulEquiv_inl` and `rightHom_changeByMulEquiv` prove that it fixes the kernel
endpoint and quotient coordinate.  M9b may bundle these commuting equations as a
`GroupExtension.Equiv`; M9a does not claim the full extension-classification theorem.

## Normalized sections and factor extraction

The section convention is:

```text
element = inl(t) * s(h),
factor defect = s(g) * s(h) * s(gh)⁻¹.
```

The structure:

```lean
structure NormalizedSection (S : GroupExtension N E H)
    extends S.Section where
  map_one : toSection 1 = 1
```

adds the normalization absent from mathlib's general `GroupExtension.Section`.
`NormalizedSection.normalize` normalizes a supplied section by left-multiplying by
`(s 1)⁻¹`; it does not choose a section.

For an extension by `Multiplicative T`:

```lean
noncomputable def NormalizedSection.factor
    (s : NormalizedSection S) (g h : H) : T
```

is characterized uniquely by:

```lean
theorem NormalizedSection.inl_factor :
  S.inl (Multiplicative.ofAdd (s.factor g h)) =
    s g * s h * (s (g * h))⁻¹
```

and the bidirectional uniqueness interface `factor_eq_iff`.  Internally, `Function.invFun` obtains
the kernel coordinate.  It cannot make a noncanonical value into a public invariant because
`S.inl_injective` proves that the coordinate is unique, and the supplied section remains an
explicit argument.

For `X : ExtensionOverAction ρ`, the construction:

```lean
noncomputable def NormalizedSection.toCocycle
    (s : NormalizedSection X.toGroupExtension) :
    NormalizedCocycle ρ
```

uses `NormalizedSection.factor_cocycle`, whose proof is the associativity calculation in `E`.

## Section change

For normalized sections `s'` and `s`, `NormalizedSection.differenceCochain s' s` is the unique
normalized cochain satisfying:

```text
s'(g) = inl(b(g)) * s(g).
```

The exact section-change theorem is:

```lean
theorem NormalizedSection.factor_change :
  factor s' g h =
    b(g) + ρ(g)(b(h)) + factor s g h - b(gh)
```

and the bundled statement is:

```lean
theorem NormalizedSection.toCocycle_change :
  s'.toCocycle X =
    (s.toCocycle X).changeBy
      (NormalizedSection.differenceCochain s' s)
```

This fixes the sign convention as `c' = c + δb`.

## Recovery and existing-project adapters

`TwistedProduct.canonicalSection` is a normalized section of the canonical twisted-product
extension.  The theorem:

```lean
TwistedProduct.canonicalSection_toCocycle :
  (TwistedProduct.canonicalSection c).toCocycle
      (TwistedProduct.toExtensionOverAction c) = c
```

proves that extension construction followed by factor extraction recovers the input cocycle.

The existing wallpaper-group exact sequence is connected without redefining it:

```lean
EuclideanMotion.pointGroupVectorExtension
EuclideanMotion.pointGroupExtensionOverAction
```

The first declaration only relabels the kernel of `pointGroupExtension G` using
`translationEquiv G`; the second proves compatibility with the already established
`pointActionHom G`.

The Version 1 dihedral section is connected by:

```lean
dihedralNormalizedSection
dihedralNormalizedSection_factor
dihedralNormalizedCocycle
dihedralFactor_cocycle
```

In particular, the existing `dihedralFactor` is definitionally interpreted through the generic
section API and is now proved to satisfy the generic cocycle identity.  No cyclic, reflection, or
dihedral classification proof was rewritten.

## Dependency and computability boundary

- The core assumes only `Group H`, `AddCommGroup T`, and an explicit action.
- It has no finiteness, freeness, rank, dimension, plane geometry, lattice, or wallpaper-label
  assumption.
- Explicit cocycles, cochains, coboundaries, twisted products, and coordinate equivalences are
  computable data.
- Only factor extraction from an arbitrary injective kernel map is `noncomputable`; its result is
  uniquely specified by `inl_factor`.
- There is no dependency on `groupCohomology.H2`, `ModuleCat`, or homological complexes.

## Deferred M9b interfaces

M9b still needs human-approved statements for:

1. bundling coboundary coordinate changes as endpoint-preserving `GroupExtension.Equiv`;
2. reconstructing an arbitrary extension from a normalized section and proving the normal-form
   equivalence with its twisted product;
3. naturality under endpoint-preserving extension equivalences;
4. the converse from extension equivalence to a coboundary relation;
5. fixed-action extension classification;
6. heterogeneous transport of kernel, quotient, and action;
7. adapters for `FiniteCosetData.shift`, the lattice-valued defect, and the existing cyclic
   `shiftClass`; and
8. the thin free-abelian rank-`n` specialization.

M9b has not started.

## Human review checklist

Please review:

1. whether `AdditiveAction H T = H →* Multiplicative (AddAut T)` is the intended public action
   representation;
2. whether the factor order `s(g)s(h)s(gh)⁻¹` and left-section-change convention are correct;
3. whether `c' = c + δb` and `(t,g) ↦ (t-b(g),g)` have the intended signs;
4. whether `ExtensionOverAction.conjugation_inl` records exactly the prescribed quotient action;
5. whether `Function.invFun` is sufficiently hidden behind the unique `inl_factor`
   characterization;
6. whether the twisted product's canonical `GroupExtension` has the intended endpoints;
7. whether the dihedral adapter is strong enough to validate compatibility with existing
   Version 1 factor calculations; and
8. whether the listed M9b boundary keeps this milestone from claiming extension classification
   prematurely.

## Validation

- All six new production modules compile as individual Lake targets.
- `lake build` succeeds with 2887 jobs.
- `git diff --check` succeeds.
- The project Lean-source scan finds no `sorry`, `admit`, `axiom`, or `unsafe`.
- The new source imports neither `groupCohomology.H2`, `ModuleCat`, nor a homological complex.
