Review status: awaiting human approval

# M9b-b2a action and cocycle transport review

## Scope

M9b-b2a implements only the action, normalized-cochain, and
normalized-cocycle transport layer approved in
[`M9B_B2_DESIGN_REVIEW.md`](M9B_B2_DESIGN_REVIEW.md).

It does not implement:

- `GroupExtension` endpoint transport;
- `ExtensionOverAction.transport`;
- heterogeneous extension equivalence or its classifier;
- `TranslationPreservingIso`, M5, M8, or `FiniteCosetData` adapters; or
- an abstract `H²` comparison.

No M9a, M9b-a, M9b-b1, Version 1, or M8 declaration was modified.

## Source module

The dimension-independent implementation is:

```text
WallpaperGroups/Extensions/Transport.lean
```

Its only project import is:

```text
WallpaperGroups.Extensions.NormalizedCocycle
```

The root `WallpaperGroups.lean` imports the module.  The transport module does
not import plane geometry, lattices, wallpaper labels, extension
classification, or homological group cohomology.

## Compatible action equivalence

The new structure is:

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

The direction is always source to target:

```text
(T, H, ρ) → (T', H', ρ').
```

The structure contains no middle group, extension, section, basis, or
noncanonical choice.

The coherence operations are:

```text
AdditiveAction.Equiv.refl
AdditiveAction.Equiv.symm
AdditiveAction.Equiv.trans
```

`symm` derives the inverse intertwining law by applying
`kernelEquiv.injective` to the original law.  `trans` composes the two endpoint
equivalences and applies the two intertwining laws in source-to-target order.

## Normalized cochain transport

The definition is:

```lean
def NormalizedCochain.transport
    (b : NormalizedCochain H T)
    (a : AdditiveAction.Equiv ρ ρ') :
    NormalizedCochain H' T'
```

with exact pointwise formula:

```text
(b.transport a)(h') =
  a.kernelEquiv (b (a.quotientEquiv.symm h')).
```

Normalization is preserved because `quotientEquiv.symm 1 = 1`,
`b 1 = 0`, and `kernelEquiv 0 = 0`.

The following coherence theorems are proved:

```text
NormalizedCochain.transport_refl
NormalizedCochain.transport_trans
NormalizedCochain.transport_symm
NormalizedCochain.symm_transport
```

They cover identity, composition, forward-then-backward transport, and
backward-then-forward transport.

## Normalized cocycle transport

The definition is:

```lean
def NormalizedCocycle.transport
    (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    NormalizedCocycle ρ'
```

with exact pointwise formula:

```text
(c.transport a)(g', h') =
  a.kernelEquiv
    (c (a.quotientEquiv.symm g')
       (a.quotientEquiv.symm h')).
```

Both normalization equations follow from the source normalization and the
endpoint equivalences.

For the cocycle identity, multiplication is first pulled back through
`quotientEquiv.symm`.  The source cocycle equation is then mapped through
`kernelEquiv`; additive naturality handles both sums, and `intertwines`
rewrites the transported action term to the target action.  No new
associativity proof or cohomology library is used.

The corresponding coherence theorems are:

```text
NormalizedCocycle.transport_refl
NormalizedCocycle.transport_trans
NormalizedCocycle.transport_symm
NormalizedCocycle.symm_transport
```

As for cochains, both inverse round trips are explicit.  No equality of action
equivalence structures with `refl` is required.

## Coboundary and `changeBy` naturality

Coboundaries commute exactly with transport:

```lean
theorem NormalizedCochain.coboundary_transport
    (b : NormalizedCochain H T)
    (a : AdditiveAction.Equiv ρ ρ') :
    (b.coboundary ρ).transport a =
      (b.transport a).coboundary ρ'
```

The proof is pointwise and uses:

```text
kernelEquiv.map_add
kernelEquiv.map_sub
a.intertwines.
```

Changing a cocycle by a coboundary is therefore exactly natural:

```lean
theorem NormalizedCocycle.changeBy_transport
    (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T)
    (a : AdditiveAction.Equiv ρ ρ') :
    (c.changeBy b).transport a =
      (c.transport a).changeBy (b.transport a)
```

This preserves the approved convention:

```text
c.changeBy b = c + δb.
```

No sign reversal is introduced.

## Cohomology-relation naturality

Transporting the explicit cochain witness gives the one-way theorem:

```lean
theorem CocycleCohomologous.transport
    (a : AdditiveAction.Equiv ρ ρ')
    {c d : NormalizedCocycle ρ}
    (h : CocycleCohomologous c d) :
    CocycleCohomologous (c.transport a) (d.transport a)
```

The main M9b-b2a relation theorem is:

```lean
theorem CocycleCohomologous.transport_iff
    (a : AdditiveAction.Equiv ρ ρ')
    (c d : NormalizedCocycle ρ) :
    CocycleCohomologous c d ↔
      CocycleCohomologous (c.transport a) (d.transport a)
```

The forward implication transports the normalized cochain witness.  The
reverse implication applies the same theorem along `a.symm`; the cocycle
round-trip simp theorems then recover `c` and `d`.

The action equivalence remains an explicit parameter.  The theorem does not
existentially quantify over endpoint equivalences and therefore does not
quotient by endpoint automorphisms.

## Complete declaration list

```text
AdditiveAction.Equiv
AdditiveAction.Equiv.kernelEquiv
AdditiveAction.Equiv.quotientEquiv
AdditiveAction.Equiv.intertwines
AdditiveAction.Equiv.refl
AdditiveAction.Equiv.symm
AdditiveAction.Equiv.trans

NormalizedCochain.transport
NormalizedCochain.transport_apply
NormalizedCochain.transport_refl
NormalizedCochain.transport_trans
NormalizedCochain.transport_symm
NormalizedCochain.symm_transport
NormalizedCochain.coboundary_transport

NormalizedCocycle.transport
NormalizedCocycle.transport_apply
NormalizedCocycle.transport_refl
NormalizedCocycle.transport_trans
NormalizedCocycle.transport_symm
NormalizedCocycle.symm_transport
NormalizedCocycle.changeBy_transport

CocycleCohomologous.transport
CocycleCohomologous.transport_iff
```

## Dependency and choice boundary

- The implementation is independent of dimension, finiteness, freeness,
  rank, topology, metrics, and plane geometry.
- All transport data is explicit and computable.
- No `Classical.choose`, section, basis, or lift occurs.
- Existing `AdditiveAction`, `NormalizedCochain`, `NormalizedCocycle`,
  `coboundary`, `changeBy`, and `CocycleCohomologous` definitions are
  unchanged.
- No extension-equivalence structure is introduced.
- No `GroupExtension`, `ExtensionOverAction`, M5/M8 adapter, `ModuleCat`,
  homological complex, or `groupCohomology.H2` is imported or implemented.

## Remaining M9b-b2 work

M9b-b2b still needs:

1. quotient and combined endpoint relabeling for `GroupExtension`;
2. `ExtensionOverAction.transport`;
3. the thin heterogeneous relation over the existing
   `GroupExtension.Equiv`; and
4. normalized-section and twisted-product transport.

M9b-b2c still needs:

1. the heterogeneous arbitrary-extension classifier; and
2. the `TranslationPreservingIso` action/extension adapter.

Neither stage began in M9b-b2a.

## Human review checklist

Please review:

1. whether `AdditiveAction.Equiv` contains exactly the intended endpoint data
   and action-intertwining law;
2. whether the source-to-target direction of `refl`, `symm`, and `trans` is
   correct;
3. whether cochain and cocycle transport correctly precompose with
   `quotientEquiv.symm`;
4. whether the transported cocycle identity uses precisely the approved
   action intertwining, without an extra assumption;
5. whether the coboundary and `changeBy` equations retain the accepted
   `c + δb` convention;
6. whether both transport round trips are sufficient for stable later
   endpoint transport;
7. whether the reverse implication of `transport_iff` correctly uses
   `a.symm`; and
8. whether the dependency and scope boundaries keep endpoint transport and
   project adapters outside M9b-b2a.

## Validation

- `lake env lean WallpaperGroups/Extensions/Transport.lean` succeeds without
  warnings.
- `lake build WallpaperGroups.Extensions.Transport` succeeds with 1074 jobs.
- The root `WallpaperGroups.lean` file compiles with the new import.
- `lake build` succeeds with 2889 jobs.
- `git diff --check` succeeds.
- The project Lean-source scan finds no `sorry`, `admit`, `axiom`, or
  `unsafe`.
- The transport module contains no endpoint-transport, M5/M8 adapter, or
  abstract `H²` implementation.
- No toolchain, dependency, Version 1, M8, M9a, M9b-a, or M9b-b1 declaration
  is modified.
