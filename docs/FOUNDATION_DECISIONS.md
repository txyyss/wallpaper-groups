# Foundation decisions

FD-001 and FD-002 close M0; later numbered entries record foundation-level choices made while
implementing their active milestone.  M0 experiments remain under `Prototype`, while stable
interfaces move into production modules only when their roadmap milestone becomes active.

## FD-001: Euclidean motions use affine isometry equivalences

- **Status:** accepted for the M1 foundation.
- **Decision:** represent a Euclidean motion of a real normed vector space `E` by
  `AffineIsometryEquiv ℝ E E` (notation `E ≃ᵃⁱ[ℝ] E`).  Add only a thin project API for
  `translationPart g := g 0`, `linearPart g := g.linearIsometryEquiv`, pure translations, and
  reconstruction from these parts.
- **Primary rejected alternative:** do not use
  `Multiplicative E ⋊ (E ≃ₗᵢ[ℝ] E)` as the primary type.  It has the correct multiplication,
  but requires a type tag, a hand-built action into `MulAut`, and a second construction before it
  can act on points as an affine isometry.  Retain it only as a possible comparison object or as
  the result of a proved splitting.
- **Other rejected alternatives:** a raw pair `(E × (E ≃ₗᵢ[ℝ] E))` would duplicate group laws;
  general affine equivalences forget the metric; matrices make the public representation depend
  on coordinates.
- **Compiling evidence:** the original M0 candidate compiled all required formulas.  M1 migrated
  it to `WallpaperGroups/Basic/EuclideanMotion.lean`, which defines the stable alias and thin
  parts API and proves the action decomposition, multiplication and inverse formulas,
  extensionality, composition of pure translations, and
  `g * translation(t) * g⁻¹ = translation(linearPart(g) t)`.  The former prototype file now
  imports the production API and serves as a regression test.
- **Expected M1--M3 effect:** M1 defines translation and point groups directly as subgroups or
  ranges of actual affine isometries and builds the kernel--range `GroupExtension`.  M2's
  equivalences act on genuine geometric transformations.  M3 can remain coordinate-free until a
  lattice basis is deliberately selected for its integral matrix argument.
- **Re-evaluate if:** the stable linear-part group homomorphism cannot be made simp-friendly,
  kernel-to-translation identification repeatedly needs semidirect internals, or a later mathlib
  release supplies a first-class Euclidean-isometry group with strictly better translation,
  reflection, and exact-sequence support.  Any change should come with a compiled equivalence and
  migration plan.

## FD-002: a rank-two lattice is an integer submodule with a chosen basis

- **Status:** accepted for the M2 foundation.
- **Decision:** use a thin wrapper whose mathematical data are

  ```lean
  carrier : Submodule ℤ E
  basis : Module.Basis (Fin 2) ℤ carrier
  basis_real_linearIndependent :
    LinearIndependent ℝ (fun i => (basis i : E))
  ```

  Treat `IsZLattice ℝ carrier` and discreteness/full-span results as derived properties when
  the ambient hypotheses imply them, rather than as the stored primary representation.
- **Primary rejected alternative:** `IsZLattice ℝ L` alone is a proposition on a
  `Submodule ℤ E` with a `DiscreteTopology` instance and full real span.  It contains no chosen
  two-element integer basis or direct coordinate map, and it cannot describe lower-rank
  intermediate sublattices.
- **Other rejected alternatives:** a bare `AddSubgroup E` makes integer-linear fixed, image,
  quotient, and matrix operations less direct; two bare vectors do not package unique integer
  coordinates; storing only an additive equivalence to `ℤ²` loses the ambient embedding and real
  independence.  Generating the carrier from a real basis is a useful constructor, not the
  general representation, because it bakes a particular frame into the value.
- **Compiling evidence:** `WallpaperGroups/Prototype/RankTwoLattice.lean` constructs the standard
  `ℤ²` in `Fin 2 → ℝ`, gives its `Module.Basis (Fin 2) ℤ`, proves real linear independence,
  defines mutually inverse integer coordinate maps, synthesizes `DiscreteTopology` and
  `IsZLattice`, and sends a lattice automorphism to both a `2 × 2` integer matrix and
  `Matrix.GeneralLinearGroup (Fin 2) ℤ`.
- **Expected M1--M3 effect:** M1 is unaffected except that its translation kernel can later be
  identified with an integer submodule.  M2 obtains canonical coordinates relative to a chosen
  basis and an exact basis-change/`GL₂(ℤ)` interface.  M3 can state the crystallographic
  restriction for integral `2 × 2` matrices and transport the conclusion back to the
  coordinate-free action.
- **Re-evaluate if:** the stable plane definition makes real independence redundant in a clean,
  proved way; topology-instance transport becomes a persistent burden; or mathlib gains a
  bundled framed `ℤ`-lattice with chosen finite basis, coordinates, and general ambient-space
  support.  A replacement must still compile the coordinate round trips and the `GL₂(ℤ)` bridge.

## Recorded API deviations from roadmap pseudocode

- Current mathlib uses the fully qualified name `Module.Basis`; roadmap identifiers are
  conceptual until checked.
- A bundled translation map into the multiplicative Euclidean-motion group uses
  `Multiplicative E →* EuclideanMotion E`, not an additive homomorphism whose codomain is a
  multiplicative group.
- `GroupExtension` already packages the short exact sequence data needed by M1; a project-local
  structure should wrap or specialize it, not duplicate its fields without a demonstrated need.

The M0 adaptations above are minimal.  They do not alter the roadmap's mathematical objects,
equivalence relation, shift-class strategy, or milestone boundaries.

## FD-003: the M1 exact sequence is a `GroupExtension`

- **Status:** accepted for the M1 exact-sequence interface.
- **Decision:** package the canonical sequence as
  `GroupExtension (translationSubgroup G) G (pointGroup G)`.  Its inclusion is the subgroup
  subtype homomorphism and its projection is the range restriction of `restrictedLinearPart G`.
  Continue to export the individual injectivity, surjectivity, and range-equals-kernel theorems
  for direct use.
- **Rejected alternatives:** do not introduce a category-theoretic short-exact-sequence layer for
  M1.  `Function.MulExact` alone is too weak because it omits endpoint injectivity and
  surjectivity; a project-local structure duplicating all five `GroupExtension` fields would add
  no information.
- **Compiling evidence:** `WallpaperGroups/Invariants/ExactSequence.lean` defines
  `pointGroupExtension`, proves the inclusion range equals the point-projection kernel, and proves
  that `GroupExtension.conjAct` agrees with the geometric point action on translation elements.
- **Expected M2--M6 effect:** later files can use the named low-level facts without importing
  more extension theory, while extension-oriented arguments can use the bundled object.  This
  does not assert a splitting and therefore preserves the non-split data needed by later shift
  classes.
- **Re-evaluate if:** M2 endpoint transport under translation-preserving isomorphisms becomes
  substantially simpler with another maintained mathlib abstraction.  Any replacement must
  retain the current five exactness facts and must not assume a splitting.
