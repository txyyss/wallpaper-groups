# Lean module-system migration policy

Decision status: adopted for the Lean 4.35 migration

Implementation status: complete

This document records the public-API policy used while migrating the project to
Lean's module system.  The migration does not change the mathematical meaning or
type of any existing definition or theorem.  It does add named observation lemmas
where downstream code should no longer depend on accidental unfolding.  In
particular, an existing declaration is not made private merely because no current
project file imports it.

The implementation follows the official [Lean module-system
reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
and its porting recipe.  Lake is configured with `requiresModuleSystem = true` so
that every library source file must remain a genuine module.

## Two independent API contracts

Public visibility and definitional exposure answer different questions:

- A public declaration may be named and used by downstream clients.  Mathematical
  vocabulary, classification objects, reviewed equivalence relations, reusable
  constructions, and theorem statements remain public even when the repository has
  no present downstream use for them.
- An `@[expose]` public definition additionally promises that downstream proofs may
  unfold its body and depend on its reduction behavior.  This stronger promise is
  reserved for stable mathematical conventions and intentionally computational data.

Thus a public opaque definition is an ordinary and intentional API.  Its stable
observation interface consists of named `_apply`, `_coe`, `_carrier`, naturality,
round-trip, or choice-independence theorems rather than accidental kernel reduction.

## Imports

| Form | Project policy |
| --- | --- |
| `public import M` | `M` is part of the module's conceptual interface, its public types, instances, notation, or syntax form an expected downstream environment, or one of its declarations occurs in public computational data whose body Lean must export. |
| `import M` | `M` is needed only by proofs or by the local implementation and is not re-exported. |
| `meta import M` | Ordinary declarations from `M` must be available at elaboration time.  A tactic module whose exported declarations are already `meta` normally needs only an ordinary private `import`. |
| `import all M` | The implementation genuinely needs another project module's private scope.  This requires a documented reason and is not a default porting device. |

`WallpaperGroups.lean` remains the stable umbrella and publicly imports every
production module.  This migration does not use the new module system to shrink the
historical meaning of `import WallpaperGroups`.  A smaller facade, if ever desired,
would be a separate API decision.  Files under `WallpaperGroups/Prototype/` remain
private regression and audit fixtures and are not imported by the umbrella.

## Visibility decisions

A declaration remains public when it is part of the project's mathematical
language, when an external user might reasonably use it to state a theorem, when it
belongs to an already reviewed V1/V2 interface, or when hiding it would force users
to duplicate a mathematical definition.  Current reference counts are not a
criterion.

A definition is exposed only when its body is itself a stable mathematical
convention, downstream reduction is useful and intended, and the body is free of
arbitrary choices or proof plumbing.  In particular, definitions based on
`Classical.choose`, arbitrary bases, lifts, or sections are public but normally
opaque.  They are observed through carrier equalities, equivalences, and
choice-independence theorems.

The policy by layer is:

- **Basic:** core ambient types and structures are public.  Translation and linear
  parts, lattice coordinates, and fixed matrix conventions may be exposed; chosen
  bases and transported witnesses remain opaque when their construction is not the
  invariant.
- **Invariants and restriction:** translation and point groups, orientation,
  crystallographic orders, shift classes, and normal-form structures are public.
  Canonical predicates and finite tables may be exposed; existence witnesses and
  proof-specific reductions are not.
- **Models:** standard model names, explicit finite-coset data, shifts, and finite
  label dispatch are public.  The reviewed transparent normal-form formulas may be
  exposed, but enumeration lemmas, membership proofs, cocycle proof witnesses, and
  matrix proof plumbing remain private or opaque.
- **Extensions:** actions, normalized cochains and cocycles, coboundaries, and the
  explicit twisted-product formulas are computational public API.  Noncanonical
  sections, reconstruction choices, and endpoint-transport implementations remain
  opaque behind their naturality and classification theorems.
- **Geometry:** the four motion predicates, discreteness, cocompactness, and the two
  textbook equivalence relations expose their reviewed definitions.  Recovered
  lattices and conversions involving basis choice are public but opaque, with
  carrier, round-trip, and choice-independence theorems as their interface.
- **Classification:** labels, signatures, canonical finite dispatch, the three
  classification layers, quotient equivalences, and cardinality theorems are public.
  Classification proof bodies and case-split plumbing are not exposed.

## Verification

The migration is checked by:

1. compiling every production module and the umbrella;
2. compiling `WallpaperGroups/Prototype/PublicAPI.lean`, which imports only
   `WallpaperGroups` and exercises representative visibility and intentional
   definitional reductions;
3. running both `lake build` and `lake --wfail build`;
4. scanning for forbidden placeholders, new axioms, and `unsafe` declarations; and
5. running `git diff --check`.

The smoke test deliberately does not assert that implementation bodies are opaque.
It tests positive, intended contracts only, so future implementation changes do not
turn the regression fixture into an accidental expansion of the API.

At completion, all 55 Lean source files are modules.  The umbrella publicly imports
all 50 production submodules and none of the four prototype fixtures.  The sole
remaining `import all` is the documented proof-only use in
`Restriction/Crystallographic.lean`.  Both the ordinary build and the
warnings-as-errors build pass, as does the root-only public-API regression module.
