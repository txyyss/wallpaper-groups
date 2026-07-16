Review status: approved

# M7 specification review

## Final label and model types

The complete exported label type in `WallpaperGroups/Models/WallpaperModels.lean` is:

```lean
inductive WallpaperType
  | p1 | p2 | p3 | p4 | p6
  | cm | pm | pg
  | cmm | pmm | pmg | pgg | p3m1 | p31m | p4m | p4g | p6m
  deriving DecidableEq, Fintype
```

`WallpaperType.model : WallpaperType → PlaneGroup` dispatches to the already proved transparent
models from M4, M5, and M6.  `WallpaperSignature` records the disjoint decomposition

```text
CrystallographicOrder + OneReflectionType + MultipleReflectionType
```

and `wallpaperSignatureEquiv : WallpaperType ≃ WallpaperSignature` proves that this is exactly
the `5 + 3 + 9` split.

## Computed model signatures

The table records the definitional value of `WallpaperType.signature`, the exact full
translation lattice from `WallpaperType.model_translationLattice`, and the finite point-group
order from `WallpaperType.model_pointGroup_card`.

| Label | Component signature | Translation lattice | Point-group order |
| --- | --- | --- | ---: |
| `p1` | no reflections, order 1 | standard square | 1 |
| `p2` | no reflections, order 2 | standard square | 2 |
| `p3` | no reflections, order 3 | hexagonal | 3 |
| `p4` | no reflections, order 4 | standard square | 4 |
| `p6` | no reflections, order 6 | hexagonal | 6 |
| `cm` | one reflection, centered | centered rectangular | 2 |
| `pm` | one reflection, primitive zero shift | standard square | 2 |
| `pg` | one reflection, primitive nonzero shift | standard square | 2 |
| `cmm` | multiple reflections, order-two centered | centered rectangular | 4 |
| `pmm` | multiple reflections, order-two `00` | standard square | 4 |
| `pmg` | multiple reflections, order-two mixed | standard square | 4 |
| `pgg` | multiple reflections, order-two `11` | standard square | 4 |
| `p3m1` | multiple reflections, order-three full axis span | hexagonal | 6 |
| `p31m` | multiple reflections, order-three index-three axis span | hexagonal | 6 |
| `p4m` | multiple reflections, order-four zero primitive shift | standard square | 8 |
| `p4g` | multiple reflections, order-four nonzero primitive shift | standard square | 8 |
| `p6m` | multiple reflections, unique order-six signature | hexagonal | 12 |

`WallpaperSignature.model_family` proves the advertised no/one/multiple reflection predicate for
every row.  The model-specific full translation-lattice and point-group proofs remain in
`Models/RotationModels.lean`, `Models/ReflectionModels.lean`, and `Models/DihedralModels.lean`.

## Component classification theorems

M4:

```lean
theorem classify_no_reflections
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    ∃! q : CrystallographicOrder,
      PlaneGroup.Equivalent G (rotationModel q)
```

M5:

```lean
theorem classify_one_reflection
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G) :
    ∃! w : OneReflectionType, PlaneGroup.Equivalent G w.model
```

M6:

```lean
theorem classify_multiple_reflections
    (G : PlaneGroup) (hG : PointGroupHasMultipleReflections G) :
    ∃! w : MultipleReflectionType, PlaneGroup.Equivalent G w.model
```

## Global classification results

Existence:

```lean
theorem exists_equivalent_wallpaperModel (G : PlaneGroup) :
    ∃ w : WallpaperType, PlaneGroup.Equivalent G w.model
```

Pairwise inequivalence of the standard labels:

```lean
theorem WallpaperType.models_equivalent_iff (w v : WallpaperType) :
    PlaneGroup.Equivalent w.model v.model ↔ w = v
```

The final unique classification theorem has the requested complete type:

```lean
theorem classification (G : PlaneGroup) :
    ∃! w : WallpaperType,
      PlaneGroup.Equivalent G (WallpaperType.model w)
```

Existence uses `pointGroup_reflection_trichotomy` followed by the appropriate component theorem.
Within-family uniqueness uses the M4/M5/M6 model iff theorem; cross-family inequivalence uses
equivalence invariance and pairwise disjointness of the three reflection-family predicates.

## Quotient and cardinality

`WallpaperGroups/Classification/PlaneGroupClasses.lean` defines

```lean
abbrev PlaneGroup.EquivalenceClass := Quotient PlaneGroup.equivalentSetoid

def WallpaperType.equivalenceClassEquiv :
    WallpaperType ≃ PlaneGroup.EquivalenceClass

theorem WallpaperType.card_eq_seventeen : Nat.card WallpaperType = 17

theorem PlaneGroup.equivalenceClass_card_eq_seventeen :
    Nat.card PlaneGroup.EquivalenceClass = 17
```

The quotient equivalence is derived only after the representative-level `∃!` theorem is stable.

## Paper correspondence and deviations

- The three component theorem blocks correspond exactly to the paper's `5 + 3 + 9` table.
- Modern labels `p4m`, `p4g`, and `p6m` represent the paper's `p4mm`, `p4mg`, and `p6mm` names.
- M7 reuses, rather than reconstructs, the standard groups proved in M4--M6.  The exported
  model interface is uniform: every model has a transparent finite-coset normal form and proved
  full translation lattice and point group.
- The theorem classifies the approved strong algebraic `PlaneGroup` definition under
  translation-preserving abstract group isomorphism.  It does not yet prove the post-v1
  discrete/cocompact bridge and does not claim classification by Euclidean conjugacy.
- No approved M2 or M3 definition or theorem statement was changed.

## Files and declarations requiring owner review

- `WallpaperGroups/Models/WallpaperModels.lean`:
  `WallpaperType`, `WallpaperType.model`, `WallpaperSignature`, `wallpaperSignatureEquiv`,
  `WallpaperType.model_translationLattice`, `WallpaperType.model_pointGroup_card`, and
  `WallpaperSignature.model_family`.
- `WallpaperGroups/Classification/Wallpaper.lean`:
  the three cross-family inequivalence lemmas, `WallpaperSignature.models_equivalent_iff`,
  `WallpaperType.models_equivalent_iff`, `exists_equivalent_wallpaperModel`, and
  `classification`.
- `WallpaperGroups/Classification/PlaneGroupClasses.lean`:
  `WallpaperType.equivalenceClassEquiv`, `WallpaperType.card_eq_seventeen`, and
  `PlaneGroup.equivalenceClass_card_eq_seventeen`.
- `README.md` and FD-015 for the exact classification object, equivalence relation, and stated
  scope.

## Final validation

- Each of the three new production files compiles directly.
- `lake build` succeeds: 2872 jobs.
- `git diff --check` succeeds; untracked production and review files also pass whitespace checks.
- The project Lean-source scan has zero `sorry`, `admit`, `axiom`, or `unsafe` matches.
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are unchanged from `m6-complete`.
- Existing non-fatal linter warnings in the M6 matrix/model implementation are replayed; the M7
  production files add no warnings.

Human review should focus on the meaning of `PlaneGroup.Equivalent`, the `5 + 3 + 9` assembly,
cross-family disjointness, the exact `∃!` statement, and whether the quotient/cardinality result
is at the intended level of abstraction.
