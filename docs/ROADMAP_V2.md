# Wallpaper Groups — Version 2 Roadmap

**Status:** active normative Version 2 roadmap.

**Baseline:** Version 1 is complete. It classifies the strong algebraic `PlaneGroup` objects into the 17 wallpaper types under translation-preserving abstract group isomorphism.

**Short-term endpoint:** complete M9b. Version 2 should strengthen the geometric interpretation of the existing theorem and extract the dimension-independent extension theory needed by a future verified space-group enumerator. It must not rewrite the completed 17-class proof unless a genuine defect is found.

## 1. Version 2 goals

Version 2 has two related but logically separate tracks.

### Geometric track

1. Relate the current equivalence to the textbook formulation that preserves translations, rotations, reflections, and glide reflections.
2. Prove that every strong algebraic `PlaneGroup` acts discretely and cocompactly on the plane.
3. Prove the converse: every discrete cocompact plane isometry group determines a strong algebraic `PlaneGroup`.
4. Derive the standard geometric statement of the 17 wallpaper-group theorem.

### Extension-theoretic track

1. Interpret the existing factor-set, finite-coset, and shift-class constructions as cocycles and coboundaries.
2. Extract a dimension-independent explicit theory of extensions of a group by an abelian group with a prescribed action.
3. Connect the generic theory back to the completed two-dimensional implementation.

The two tracks may share algebraic infrastructure, but M9a and M9b must not depend on completion of the difficult converse geometric bridge if that bridge becomes a separate Bieberbach-scale project.

## 2. Project principles

1. **Preserve Version 1.** Existing public definitions and theorems remain stable unless a proved incompatibility forces a reviewed change.
2. **Use local audits, not repeated global audits.** Existing API and design records are the default. Search mathlib or write a small probe only when a concrete implementation question arises.
3. **Review definitions before long proofs.** The exact geometric notions of discreteness and cocompactness require owner approval before the reverse bridge is developed.
4. **Keep the extension core dimension-independent.** M9 code must not depend on `Plane`, `Fin 2`, Euclidean metrics, crystallographic orders, or wallpaper labels.
5. **Prefer explicit computable structures before abstract cohomology.** Normalized cocycles, coboundaries, twisted products, sections, and extension equivalences are the primary objects. Identification with a pre-existing `H²` object is optional later work.
6. **Do not confuse equivalence relations.** Version 2 still does not classify groups up to Euclidean conjugacy; that relation retains continuous metric moduli.
7. **Stop on specification changes, not routine proof difficulty.** Ordinary Lean/API problems are implementation work. Any need to change an approved mathematical definition or theorem statement is a human-review point.

## 3. Milestones

## M8a — Motion-type equivalence bridge

**Goal:** connect the current translation-preserving equivalence with the textbook equivalence that preserves the four types of plane motions.

### Tasks

- Define precise predicates for translations, rotations, reflections, and glide reflections of the plane.
- Prove the relevant decomposition and disjointness facts for elements of a `PlaneGroup`, including the treatment of the identity convention.
- Define the textbook-style structure consisting of an abstract group isomorphism that preserves all four motion types in both directions.
- Prove that every `TranslationPreservingIso` preserves the other three motion types automatically, using the induced real-linear conjugacy, determinant sign, and the square of an orientation-reversing motion.
- Prove that the textbook-style equivalence and `PlaneGroup.Equivalent` are logically equivalent.
- Derive a 17-class corollary stated using the textbook-style equivalence.

### Acceptance criteria

- The four predicates match the standard classification of plane isometries.
- No metric-preservation or ambient-conjugacy assumption is added.
- The new 17-class theorem is a corollary of the existing classifier, not a second classification proof.
- The exact motion-type definitions receive human specification review.

## M8b — Strong plane groups are discrete and cocompact

**Goal:** prove the easier direction from the current strong algebraic definition to a geometric wallpaper-group action.

### Definition gate

Before the main proof, choose and document the exact formal notions of:

- a discrete subgroup or discrete action; and
- a cocompact action.

Prefer a formulation that is standard, usable with current mathlib, and supports the reverse implication. A compact covering set may be used as the primary cocompactness witness; an equivalence with compactness of the orbit quotient may be added when the topology is manageable.

The chosen definition must be approved before it becomes the basis of M8c.

### Tasks

- Derive discreteness of a `RankTwoLattice` in the plane from its integer basis.
- Construct a compact fundamental parallelogram or another compact covering set for the translation lattice.
- Use finiteness of the point group and the exact sequence to control the full motion group by finitely many translation cosets.
- Prove that every `PlaneGroup` satisfies the selected geometric discreteness and cocompactness conditions.
- Package the result as a canonical conversion or theorem from `PlaneGroup` to the geometric notion without changing the underlying motion subgroup.

### Acceptance criteria

- The proof uses the existing rank-two lattice and finite point-group fields rather than adding new hypotheses.
- The result applies uniformly to all 17 standard models.
- The geometric definition and the strong-to-geometric theorem are documented and reviewed.

## M8c — Discrete cocompact groups yield strong plane groups

**Goal:** prove the substantive converse and derive the standard geometric classification theorem.

### Tasks

- Starting from a discrete cocompact subgroup of plane Euclidean motions, prove that its full pure-translation subgroup is a rank-two lattice.
- Prove that the point group is finite.
- Construct a `PlaneGroup` with exactly the original motion subgroup.
- Prove independence, up to the approved equivalence, of any auxiliary basis or compact-domain choices used in the construction.
- Establish the appropriate round-trip and compatibility theorems between the geometric and strong formulations.
- Derive a unique classification theorem for geometric wallpaper groups by `WallpaperType`.

### Acceptance criteria

- The theorem does not assume the desired rank-two lattice or finite point group under another name.
- No unproved form of the Bieberbach theorem is introduced as an axiom.
- The final theorem clearly states both the geometric object and the equivalence relation being classified.
- The construction and theorem receive human specification review.

### Decision rule

This is the highest-risk Version 2 milestone. If current topology and group-action infrastructure makes the proof a substantially larger Bieberbach project, stop with a precise design report. M9a and M9b may then proceed independently, but M8c must be recorded as deferred rather than weakened or silently declared complete.

## M9a — Factor sets, cocycles, and the existing shift invariants

**Goal:** give the completed two-dimensional extension machinery its standard cocycle interpretation without rewriting the classification.

### Tasks

- For a group extension with a normalized section, define the associated factor set in the translation group.
- Prove normalization and the 2-cocycle identity.
- Prove that changing the section changes the factor set by a coboundary.
- Prove naturality under endpoint-preserving extension equivalences.
- Relate `FiniteCosetData.shift` to a cocycle in the ambient vector space modulo the lattice, and relate its lattice-valued defect to the factor set.
- Explain formally how the existing quotient-valued `shiftClass` for a finite cyclic subgroup is obtained from the restricted extension data and why lift independence is a coboundary phenomenon.
- Add adapters and interpretation theorems; do not replace the M4–M7 proofs with cohomological arguments.

### Acceptance criteria

- Cocycle sign and multiplication conventions are explicit and tested against existing finite-coset models.
- Section change is proved by an explicit coboundary formula.
- The relationship to `shiftClass` is a theorem, not only prose.
- The existing Version 1 classification API remains unchanged.
- The cocycle conventions and interpretation receive human review.

## M9b — Dimension-independent explicit extension theory

**Goal:** extract a reusable algebraic core suitable for a future verified space-group enumeration project.

### Core setting

The primary theory should work for:

- a group `H`;
- an abelian group `T`; and
- a specified action of `H` on `T` by additive automorphisms.

Finiteness of `H` and freeness or finite rank of `T` belong in later computational layers, not in the basic extension construction unless a theorem genuinely needs them.

### Tasks

- Define normalized 2-cocycles and coboundaries for the prescribed action.
- Define cohomology at the explicit quotient/equivalence-relation level needed by the project, without requiring a full general cohomology library.
- Construct the twisted-product group attached to a cocycle:

  ```text
  (t, h) * (u, k) = (t + h • u + c(h, k), h k).
  ```

- Prove its canonical short exact sequence and induced action.
- Extract a cocycle from an extension equipped with a normalized section.
- Construct an explicit equivalence between the original extension and the twisted product obtained from its section.
- Prove that cohomologous cocycles yield endpoint-preserving equivalent extensions.
- Prove the converse at the appropriate level: an endpoint-preserving extension equivalence induces the corresponding coboundary relation.
- State a dimension-independent extension-classification theorem for a fixed action.
- Provide adapters showing that the current translation–point-group extensions and finite-coset models instantiate the generic theory.
- Add a thin specialization for free abelian lattices of rank `n` sufficient to state the input type of a future space-group catalog, without implementing that catalog.

### Acceptance criteria

- The core imports no plane geometry, rank-two matrix classification, or wallpaper models.
- Section extraction and twisted-product reconstruction are proved mutually compatible up to the stated extension equivalence.
- Cocycle equivalence and extension equivalence agree in both directions for the fixed action.
- Existing two-dimensional extension constructions are connected by proved adapters or comparison theorems.
- The exported API is usable with `T ≅ ℤ^n` and a finite integral point-group action.
- The final generic theorem receives human specification review.

## 4. Dependencies and execution order

Default order:

```text
M8a → M8b → M8c → M9a → M9b
```

The algebraic dependency is weaker:

```text
M8a → M8b → M8c
M9a → M9b
```

M9a may begin before M8c is complete if the owner explicitly defers the reverse geometric bridge. M9b depends on M9a, not on M8c.

Each milestone should be implemented and verified separately. Routine milestone prompts should contain only the current goal, special stopping point, and commit/review policy; the roadmap and repository instructions carry the persistent context.

## 5. Suggested source organization

Adapt names to the actual dependency graph.

```text
WallpaperGroups/
  Geometry/
    MotionType.lean
    GeometricWallpaperGroup.lean
    StrongToGeometric.lean
    GeometricToStrong.lean
  Extensions/
    Action.lean
    NormalizedCocycle.lean
    Coboundary.lean
    TwistedProduct.lean
    Section.lean
    Classification.lean
    WallpaperAdapters.lean
```

Do not move stable Version 1 files merely to fit this sketch.

## 6. Explicit non-goals for Version 2

Version 2 does not include:

- classification up to Euclidean conjugacy or similarity;
- moduli spaces of lattice metrics;
- the full Bieberbach theorems in arbitrary dimension;
- classification of finite subgroups of `GL_n(ℤ)`;
- normalizer or orbit-enumeration algorithms;
- verification of CARAT or another existing implementation;
- computation of a new term of OEIS A006227;
- three-dimensional space-group classification;
- a complete general-purpose group-cohomology library;
- a recognizer from arbitrary finite presentations.

These belong to a later roadmap for a verified space-group enumerator.

## 7. Version 2 definition of done

The short-term Version 2 program is complete when:

- the textbook motion-type equivalence is proved equivalent to the current relation;
- the strong-to-geometric bridge is complete;
- the geometric-to-strong bridge and geometric 17-class theorem are complete, unless the owner has explicitly recorded M8c as a separate deferred Bieberbach project;
- existing factor sets and shift classes have a proved cocycle/coboundary interpretation;
- the dimension-independent explicit extension-classification theorem is complete;
- current two-dimensional extensions are connected to the generic theory;
- the repository builds in CI without forbidden placeholders or new axioms;
- all new foundational definitions and final bridge theorems have passed human specification review.

The next project after M9b should have a separate roadmap for a verified, certificate-producing space-group enumerator.

## 8. Migration from the Version 1 roadmap

The coarse post-v1 entries currently called M8 and M9 are superseded by this document.

Recommended documentation change:

- keep `docs/ROADMAP.md` as the completed Version 1 roadmap;
- remove its M8 and M9 sections as active milestones and replace them with a short pointer to `docs/ROADMAP_V2.md`;
- replace the two coarse `Post-v1` checkboxes in `docs/PROGRESS.md` with M8a, M8b, M8c, M9a, and M9b checklists;
- update `AGENTS.md` and `docs/AGENTS.md` so Codex reads the Version 2 roadmap for active post-v1 work;
- update the README to link to Version 2 while continuing to state exactly what Version 1 has already proved.

Git history preserves the original M8/M9 placeholders, so removing them from the active Version 1 plan loses no historical information and avoids treating obsolete broad placeholders as executable specifications.
