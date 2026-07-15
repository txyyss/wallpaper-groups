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

## FD-004: the ambient plane is mathlib's Euclidean two-space

- **Status:** accepted.
- **Decision:** define `Plane` as `EuclideanSpace ℝ (Fin 2)`.  Export its finrank theorem and a
  thin canonical real-basis interface, while keeping public group and lattice definitions free of
  coordinate projections.
- **Rejected alternative:** `Fin 2 → ℝ` was useful for the M0 coordinate experiment but does not
  itself advertise the intended Euclidean inner-product geometry.  A project-local pair type
  would duplicate mathlib instances and later orientation/reflection bridges.
- **M3 effect:** the norm, inner product, finite-dimensional, and orthonormal-basis APIs are
  available directly for crystallographic restriction.  Re-evaluate only if a future mathlib
  release supplies a more canonical bundled two-dimensional Euclidean-space type.

## FD-005: the formal rank-two lattice realizes FD-002 directly

- **Status:** accepted.
- **Decision:** the production `RankTwoLattice E` has exactly the three FD-002 fields: an integer
  `Submodule`, a chosen `Fin 2` integer `Module.Basis`, and real linear independence of the two
  ambient basis vectors.  Coordinates, the derived real basis, full real span in `Plane`, matrix
  representations, and real-linear extension are theorems or definitions built from these
  fields.
- **Computational frame:** the chosen basis is deliberately part of the framed lattice value so
  coordinates are computable and matrices are explicit.  It is not required to be preserved by
  `TranslationPreservingIso`, and M2 proves equivalence after reframing.
- **Still rejected:** discreteness, `IsZLattice`, shortest vectors, and metric normal forms are not
  stored.  They remain possible derived results in milestones where they are mathematically used.

## FD-006: a plane group binds the full translation carrier by equality

- **Status:** accepted.
- **Decision:** store a motion subgroup, a `RankTwoLattice Plane`, the equality

  ```text
  translationLattice.carrier =
    (translationVectors carrier).toIntSubmodule
  ```

  and `Finite (pointGroup carrier)`.  The equality is intentionally exact: it excludes both a
  proper and a finite-index stored sublattice while allowing thin rewrite and additive-equivalence
  interfaces.
- **Rejected alternatives:** merely storing containment or finite index weakens the paper's
  definition.  Storing a second independent basis directly on the M1 additive subgroup reduces
  one transport but obscures the reusable lattice API.  `Fintype` is not stored; enumeration may
  install `Fintype.ofFinite` locally.
- **Boundary:** discreteness, cocompactness, orientation, rotations/reflections, shortest vectors,
  shifts, and classification labels are not fields.

## FD-007: translation preservation is subgroup-map equality

- **Status:** accepted.
- **Decision:** `TranslationPreservingIso G G'` stores an abstract
  `G.carrier ≃* G'.carrier` and equality between the image of the entire source translation
  subgroup and the target translation subgroup.  This form gives membership iff, restriction,
  inverse, and composition through maintained `Subgroup.map` APIs.
- **Rejected alternatives:** one-sided containment does not express “onto.”  Ambient Euclidean
  conjugacy, affine conjugacy, isometry, norm preservation, and chosen-basis preservation are all
  stronger than the equivalence on printed page 127 and would retain metric parameters that the
  17-class theorem intentionally forgets.

## FD-008: the induced point-group equivalence is canonical quotient transport

- **Status:** accepted.
- **Decision:** identify `G / translationSubgroup G` with `pointGroup G` using
  `QuotientGroup.quotientKerEquivRange (restrictedLinearPart G)`, transport the quotient through
  `QuotientGroup.congr`, and identify the target quotient with its point group.  The resulting map
  commutes with `pointProjection` by construction.
- **Rejected alternative:** choosing an arbitrary lift for every point-group element adds
  noncanonical choice and a duplicate well-definedness proof.  The quotient construction records
  exactly the kernel argument suppressed in the paper.

## FD-009: lattice equivalences extend through cast inverse matrices

- **Status:** accepted.
- **Decision:** represent a lattice equivalence and its inverse in the selected integer bases,
  cast both matrices along `ℤ → ℝ`, and use `Matrix.toLinOfInv` between the derived real bases.
  Prove separately that the resulting `Plane ≃ₗ[ℝ] Plane` agrees with the integer map on every
  lattice element.
- **Rejected alternatives:** merely matching selected basis indices does not extend an arbitrary
  lattice equivalence.  `restrictScalars` runs in the wrong direction, and the relevant generic
  scalar-extension helpers do not apply to `ℤ → ℝ`.
- **Metric warning:** this construction is an ordinary real-linear equivalence.  It is not stored
  or claimed as a `LinearIsometryEquiv`, because the paper's `λ` need not preserve lengths or
  angles.

## FD-010: matrix composition follows mathlib's column-vector convention

- **Status:** accepted.
- **Decision:** use the compiled identity

  ```text
  toMatrix (f.comp g) = toMatrix f * toMatrix g
  ```

  with source coordinates as columns and target coordinates as rows.  Consequently an
  intertwiner `f ∘ A = B ∘ f` gives `P * A = B * P`, and hence
  `B = P * A * P⁻¹`.
- **Public-invariant policy:** raw matrices depend on the selected lattice basis.  The public
  invariant is the coordinate-free lattice action; basis changes and translation-preserving
  equivalences produce proved `GL₂(ℤ)` conjugacies.

## FD-011: restriction uses trace and Cayley–Hamilton; orbit bases use shortest vectors

- **Status:** accepted.
- **Decision:** prove the crystallographic order restriction by casting the integral lattice-action
  trace to the real trace of the ambient plane isometry.  Bound that trace in `[-2, 2]`, use
  positive determinant to obtain determinant `1`, and apply the two-dimensional
  Cayley–Hamilton identity.  This gives the exact orders `1`, `2`, `3`, `4`, and `6` without any
  analytic approximation of angles.
- **Normal-form supplement:** use a shortest-vector argument only for the distinct task of
  producing the later classification basis.  A rank-two lattice is first identified with the
  integer span of its real basis, so bounded intersections are finite and a shortest nonzero
  vector exists.  For trace `c = -1, 0, 1`, nearest-integer reduction in the real orbit frame
  `(t, A t)` bounds a nonzero coordinate remainder by `3/4 * ‖t‖²`, contradicting minimality.
  Thus `(t, A t)` is an integer basis and its action matrix is `!![0, -1; 1, c]`.
- **Rejected route for the order restriction:** the paper's full shortest-vector/angle argument
  would duplicate the shortest-vector infrastructure and require more angle case analysis than
  the compiled trace bridge.  It is therefore not maintained as a second restriction proof.
  Conversely, classifying torsion matrices in `SL₂(ℤ)` up to integral conjugacy would require
  arithmetic normal-form machinery not otherwise needed; the direct orbit-basis proof is shorter
  and yields the actual vector required by M4–M6.
- **Orientation and point-group boundary:** the orientation-preserving subgroup is the
  positive-real-determinant subgroup.  It is proved cyclic through an injective complex rotation
  parameter.  A reversing element is an involution and conjugates every positive element to its
  inverse.  The exported `DihedralData` records this cyclic subgroup, a reversing generator, and
  the two-coset normal form, including the trivial-rotation boundary case.
- **Review boundary:** no field or meaning of `PlaneGroup`, `TranslationPreservingIso`, or the M2
  lattice action is changed.  The project owner approved this decision with the M3 specification.

## FD-012: no-reflection models use transparent symmorphic normal forms

- **Status:** accepted.
- **Decision:** represent each of `p1`, `p2`, `p3`, `p4`, and `p6` by a transparent symmorphic
  carrier whose translation part lies in an explicit rank-two lattice and whose linear part lies
  in the cyclic subgroup generated by an explicit lattice rotation.  The square lattice supplies
  orders `1`, `2`, and `4`; a sheared copy supplies the triangular-lattice orders `3` and `6`.
  Membership, the full translation lattice, and the point group are therefore computed from a
  proved normal form instead of inferred from an unstructured subgroup closure.
- **Extension comparison:** a nonidentity positive plane rotation fixes only zero, so every lift
  has trivial power at the point order.  The point-group extension consequently splits.  Groups
  with the same rotation order are compared by the coordinate-preserving equivalence between the
  M3 lattice-action bases and mathlib's split-extension/semidirect-product API.  The resulting
  isomorphism is proved to map the complete translation subgroup onto the target one.
- **Invariant:** the public five-valued invariant is `CrystallographicOrder`, recovered from the
  point-group cardinality.  Equal values give the extension isomorphism above; unequal values are
  obstructed by invariance of point-group cardinality.
- **M5 boundary:** M4 proves vanishing of the raw full-period translation for nontrivial positive
  rotations.  It deliberately does not introduce a general raw-vector invariant.  The canonical
  quotient-valued shift class, norm map, lift independence, and reflection computations remain a
  single coherent API for M5.

## FD-013: one-reflection classes use quotient shifts and integral reflection normal forms

- **Status:** accepted.
- **Decision:** the invariant of a finite-order point element is its lift-power translation in
  the quotient of fixed translations by the finite norm image.  Lift independence and transport
  under `TranslationPreservingIso` are proved before specializing to reflections, so no raw shift
  vector is treated as canonical.  For an integral reflection on a rank-two lattice, an exact
  basis reduction yields the primitive matrix `!![1, 0; 0, -1]` or the centered matrix
  `!![1, 1; 0, -1]`.
- **Classification:** every centered fixed translation lies in the norm image and gives `cm`.
  In the primitive form the quotient has exactly the zero class and the class of the first basis
  vector, represented by `pm` and `pg`.  The transparent models use two explicit lattice cosets;
  the reusable two-coset extension isomorphism compares actions and shifts modulo a norm.
- **Inequivalence:** centered versus primitive is detected by whether the first fixed basis vector
  is a norm.  The primitive mirror/glide distinction is detected by zero versus nonzero quotient
  shift class, using functoriality and lift independence.
- **M6 boundary:** paired reflections, their compatibility relation, and joint dihedral lattice
  normal forms are not inferred from the single-reflection dichotomy and remain M6 work.
