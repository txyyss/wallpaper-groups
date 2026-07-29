Review status: awaiting human approval

# M9b-b2b endpoint transport review

## Scope

M9b-b2b connects the approved action-equivalence transport layer to
mathlib's existing `GroupExtension`.  This snapshot implements only:

- quotient relabeling for a short exact sequence;
- simultaneous kernel and quotient endpoint transport;
- transport of an `ExtensionOverAction`; and
- identity, composition, and both inverse round-trip coherence laws.

The project owner's implementation request narrows this snapshot relative to
the broader staging suggested in
[`M9B_B2_DESIGN_REVIEW.md`](M9B_B2_DESIGN_REVIEW.md).  The thin heterogeneous
relation, normalized-section transport, twisted-product transport, final
heterogeneous classifier, and project adapters remain later work.  This is a
staging refinement, not a change to the approved endpoint-transport
mathematics.

No existing `GroupExtension.Equiv` or project mathematical definition was
changed.

## Source and dependency boundary

The implementation is in:

```text
WallpaperGroups/Extensions/EndpointTransport.lean
```

It imports only:

```text
WallpaperGroups.Extensions.Transport
```

The root `WallpaperGroups.lean` imports the new module.  The implementation is
independent of dimension, topology, lattices, plane geometry, wallpaper
labels, chosen sections, and group cohomology.

## Quotient relabeling

The new definition has type:

```lean
def GroupExtension.relabelQuotient
    (S : GroupExtension N E H)
    (e : H ≃* H') :
    GroupExtension N E H'
```

Its endpoint maps are exactly:

```text
inl' n       = S.inl n
rightHom' x  = e (S.rightHom x).
```

These formulas are exported as:

```text
GroupExtension.relabelQuotient_inl
GroupExtension.relabelQuotient_rightHom
```

The middle group `E` and kernel inclusion are unchanged.  Injectivity of `e`
shows that postcomposition does not change the kernel of the quotient
projection, while surjectivity of `e` composes with
`S.rightHom_surjective`.  Thus the original exactness proof is transported
without a choice.

## Combined endpoint transport

The combined source-to-target operation is:

```lean
def GroupExtension.transportEndpoints
    (S : GroupExtension N E H)
    (eN : N ≃* N')
    (eH : H ≃* H') :
    GroupExtension N' E H' :=
  (S.relabelKernel eN.symm).relabelQuotient eH
```

The implementation uses the equivalent explicit-function expression.  Its
maps satisfy:

```text
inl' n'      = S.inl (eN.symm n')
rightHom' x  = eH (S.rightHom x).
```

The inverse on `eN` is required by the existing
`GroupExtension.relabelKernel` convention.  The middle group remains
definitionally the same type `E`.

The formulas are exported as:

```text
GroupExtension.transportEndpoints_inl
GroupExtension.transportEndpoints_rightHom
```

## Transport over an explicit action

For:

```text
ρ  : AdditiveAction H T
ρ' : AdditiveAction H' T'
X  : ExtensionOverAction (E := E) ρ
a  : AdditiveAction.Equiv ρ ρ'
```

the new definition is:

```lean
def ExtensionOverAction.transport
    (X : ExtensionOverAction (E := E) ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    ExtensionOverAction (E := E) ρ'
```

It invokes `GroupExtension.transportEndpoints` with:

```text
eN = AddEquiv.toMultiplicative a.kernelEquiv
eH = a.quotientEquiv.
```

Consequently:

```text
(X.transport a).inl (ofAdd t') =
  X.inl (ofAdd (a.kernelEquiv.symm t'))

(X.transport a).rightHom x =
  a.quotientEquiv (X.rightHom x).
```

These are:

```text
ExtensionOverAction.transport_inl
ExtensionOverAction.transport_rightHom
```

The target-action compatibility proof applies the inverse form of
`a.intertwines`:

```text
a.kernelEquiv.symm
    (ρ'.apply (a.quotientEquiv h) t') =
  ρ.apply h (a.kernelEquiv.symm t').
```

It then reuses `X.conjugation_inl`.  There is no extra action hypothesis,
chosen section, chosen basis, or reconstructed middle group.

## Coherence

Endpoint transport satisfies propositional, rather than merely pointwise,
equalities:

```text
GroupExtension.transportEndpoints_refl
GroupExtension.transportEndpoints_trans
GroupExtension.transportEndpoints_symm
GroupExtension.symm_transportEndpoints
```

These respectively prove identity, composition, forward-then-backward, and
backward-then-forward transport.

The action-compatible wrapper has the corresponding laws:

```text
ExtensionOverAction.transport_refl
ExtensionOverAction.transport_trans
ExtensionOverAction.transport_symm
ExtensionOverAction.symm_transport
```

The equalities are propositional structure equalities.  No claim of
judgmental equality is made, and no second notion of extension equivalence is
introduced.

## Complete declaration list

```text
GroupExtension.relabelQuotient
GroupExtension.relabelQuotient_inl
GroupExtension.relabelQuotient_rightHom
GroupExtension.transportEndpoints
GroupExtension.transportEndpoints_inl
GroupExtension.transportEndpoints_rightHom
GroupExtension.transportEndpoints_refl
GroupExtension.transportEndpoints_trans
GroupExtension.transportEndpoints_symm
GroupExtension.symm_transportEndpoints

ExtensionOverAction.transport
ExtensionOverAction.transport_inl
ExtensionOverAction.transport_rightHom
ExtensionOverAction.transport_refl
ExtensionOverAction.transport_trans
ExtensionOverAction.transport_symm
ExtensionOverAction.symm_transport
```

Private structure-extensionality helpers are proof implementation details and
are not part of the exported interface.

## Deferred work and invariants

This snapshot does not implement:

- a thin heterogeneous `EquivAlong` relation;
- normalized-section or twisted-product transport;
- the final heterogeneous extension classifier;
- a `TranslationPreservingIso` or geometric-wallpaper adapter;
- M5 `ShiftClass`, `FiniteCosetData`, or cyclic-period adapters; or
- an abstract `H²` comparison.

It does not modify `GroupExtension`, `GroupExtension.Equiv`,
`ExtensionOverAction`, `AdditiveAction.Equiv`, Version 1, M8, M9a, M9b-a,
M9b-b1, or M9b-b2a declarations.  M9b-b2c/M9b-b3 has not started.

## Human review checklist

Please review:

1. whether `relabelQuotient` preserves exactness with the displayed
   postcomposition convention;
2. whether `transportEndpoints` correctly uses `eN.symm` and `eH`;
3. whether every construction truly keeps the middle group unchanged;
4. whether `ExtensionOverAction.transport` derives the target conjugation
   action from exactly `a.intertwines`;
5. whether identity, composition, and both inverse coherence laws have the
   intended directions and sufficient strength;
6. whether propositional structure equality is an appropriate coherence
   interface here;
7. whether reusing, rather than redefining, `GroupExtension.Equiv` preserves
   the approved architecture; and
8. whether all classifier and adapter work remains outside this snapshot.

## Validation

- `lake env lean WallpaperGroups/Extensions/EndpointTransport.lean` succeeds
  without warnings.
- `lake build WallpaperGroups.Extensions.EndpointTransport` succeeds with
  1075 jobs.
- The root `WallpaperGroups.lean` compiles with the new import.
- The final full `lake build` succeeds with 2890 jobs.
- `git diff --check` succeeds.
- The project Lean-source scan finds no `sorry`, `admit`, `axiom`, or
  `unsafe`.
- No toolchain or dependency configuration changed.
- No Version 1, M8, M9a, M9b-a, M9b-b1, or M9b-b2a source declaration
  changed.
