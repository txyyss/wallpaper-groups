Review status: approved

# M9b-b1 arbitrary fixed-action extension classification review

## Scope

M9b-b1 extends the approved M9b-a results from canonical twisted products to
arbitrary extensions over one fixed explicit action.  It reuses:

- M9a section-change by an explicit coboundary;
- M9b-a normalized-section transport and exact cocycle naturality;
- M9b-a twisted-product reconstruction; and
- M9b-a classification of canonical twisted products.

This stage adds no new extension-equivalence definition and no quotient over
all possible middle-group types.  It does not implement heterogeneous
kernel/quotient/action transport, the M5 `shiftClass` adapter,
`FiniteCosetData` adapters, or an abstract `H²` adapter.

No Version 1, M8, M9a, or M9b-a definition was modified.

## Source module

The two new theorems extend:

```text
WallpaperGroups/Extensions/Classification.lean
```

No new dependency is added to the root import graph.

## Arbitrary extension reconstruction

M9b-a already proved the required reconstruction theorem:

```lean
noncomputable def NormalizedSection.twistedProductExtensionEquiv
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension) :
    (TwistedProduct.toGroupExtension (s.toCocycle X)).Equiv
      X.toGroupExtension
```

Thus M9b-b1 reuses this endpoint-preserving equivalence rather than defining a
second reconstruction.  Its normal form remains:

```text
(t, h) ↦ X.inl (Multiplicative.ofAdd t) * s(h).
```

The kernel and quotient endpoint equations remain those proved in M9b-a:

```lean
NormalizedSection.normalFormHom_inl
NormalizedSection.rightHom_normalFormHom
```

## Independence from the normalized section

For one extension over `ρ` and any two normalized sections, M9b-b1 proves:

```lean
theorem NormalizedSection.toCocycle_cocycleCohomologous
    (X : ExtensionOverAction (E := E) ρ)
    (s t : NormalizedSection X.toGroupExtension) :
    CocycleCohomologous (s.toCocycle X) (t.toCocycle X)
```

The witness is exactly:

```lean
NormalizedSection.differenceCochain t s
```

because M9a proved:

```text
toCocycle(t) =
  toCocycle(s).changeBy (differenceCochain t s).
```

This direction is important: reversing `s` and `t` would produce the inverse
coboundary convention rather than the theorem's stated witness.

The theorem quantifies over arbitrary supplied sections.  A selected section
therefore never becomes a public invariant; only the explicit
`CocycleCohomologous` class is stable.

## Pairwise classifier for arbitrary extensions

The main M9b-b1 theorem is:

```lean
theorem ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous
    (X : ExtensionOverAction (E := E) ρ)
    (Y : ExtensionOverAction (E := E') ρ)
    (s : NormalizedSection X.toGroupExtension)
    (t : NormalizedSection Y.toGroupExtension) :
    Nonempty (X.toGroupExtension.Equiv Y.toGroupExtension) ↔
      CocycleCohomologous (s.toCocycle X) (t.toCocycle Y)
```

The kernel `Multiplicative T`, quotient `H`, and action `ρ` are fixed.  The
middle-group types `E` and `E'` may differ.

### Forward direction

Given:

```lean
e : X.toGroupExtension.Equiv Y.toGroupExtension
```

the source section is transported to:

```lean
s.equivComp e : NormalizedSection Y.toGroupExtension.
```

M9b-a gives the exact equality:

```text
toCocycle(s.equivComp e) = toCocycle(s).
```

The new section-independence theorem compares `s.equivComp e` with `t`.
Rewriting by exact naturality yields:

```text
CocycleCohomologous (toCocycle(s)) (toCocycle(t)).
```

The concrete forward witness is:

```text
differenceCochain t (s.equivComp e).
```

### Reverse direction

Given cohomologous section cocycles, M9b-a supplies an endpoint-preserving
equivalence between their canonical twisted products.  M9b-b1 composes:

```text
X
  ≃ twistedProduct(toCocycle(s))
  ≃ twistedProduct(toCocycle(t))
  ≃ Y.
```

In Lean the directions are:

```text
(twistedProductExtensionEquiv X s).symm
  → canonical twisted-product equivalence
  → twistedProductExtensionEquiv Y t.
```

Every component is a mathlib `GroupExtension.Equiv`, so the composite keeps
both endpoints fixed.

## Classification strength and choice boundary

The theorem is a dimension-independent, relation-level classification of
arbitrary extensions for one fixed action:

```text
endpoint-preserving extension equivalence
  ↔
normalized cocycle equivalence by an explicit coboundary.
```

It is independent of section choice because the statement holds for every
explicit pair `s`, `t`, and because any two section cocycles are separately
proved cohomologous.

M9b-b1 deliberately does not:

- choose a canonical section;
- expose a chosen cocycle as an invariant;
- bundle all middle-group types into one large quotient;
- identify different kernel or quotient types;
- quotient by endpoint automorphisms; or
- import general group cohomology.

## Complete list of new declarations

```text
NormalizedSection.toCocycle_cocycleCohomologous
ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous
```

## Relationship with M9b-a

M9b-a supplied all construction-level ingredients:

1. coboundary changes between canonical twisted products;
2. section transport and exact naturality;
3. reconstruction of an arbitrary extension from a section cocycle; and
4. the canonical twisted-product iff theorem.

M9b-b1 adds only the two comparison theorems needed to assemble those
ingredients into the arbitrary-extension classifier.  No M9b-a theorem is
reproved or weakened.

## Deferred M9b work

Later M9b stages still need:

1. heterogeneous kernel, quotient, and action transport;
2. the `TranslationPreservingIso` transport adapter;
3. cyclic-period comparison with the existing M5 `shiftClass`;
4. quotient-valued and lattice-factor `FiniteCosetData` adapters;
5. the thin free-abelian rank-`n` specialization;
6. optional, isolated comparison with mathlib `H²`; and
7. the final generic M9b review.

No work on these items began in M9b-b1.

## Human review checklist

Please review:

1. whether the arbitrary classifier has exactly the intended fixed kernel,
   quotient, and action;
2. whether quantifying over arbitrary supplied normalized sections expresses
   the required choice independence;
3. whether `differenceCochain t s` has the correct direction;
4. whether exact transport naturality is used correctly in the forward
   implication;
5. whether the reconstruction equivalences are composed in the correct
   direction in the reverse implication;
6. whether `Nonempty GroupExtension.Equiv` remains the correct relation-level
   conclusion; and
7. whether the exclusions above keep heterogeneous transport and adapters
   outside M9b-b1.

## Validation

- `lake build WallpaperGroups.Extensions.Classification` succeeds with 1104
  jobs.
- The root `WallpaperGroups.lean` file compiles.
- `lake build` succeeds with 2888 jobs.
- `git diff --check` succeeds.
- The project Lean-source scan finds no `sorry`, `admit`, `axiom`, or
  `unsafe`.
- No toolchain, dependency, Version 1, M8, M9a, or M9b-a source declaration is
  modified.
