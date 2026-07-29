# Progress

The first unchecked milestone is the active milestone.  M0–M7 record the
completed Version 1 work; M8a onward follows the active
[`docs/ROADMAP_V2.md`](ROADMAP_V2.md).

**Version 2 M8 status:** complete.  The geometric bridge is finished and
reviewed.  M9a's explicit cocycle core, M9b-a's fixed-action
extension-equivalence core, and M9b-b1's arbitrary fixed-action classifier are
complete and reviewed.  The M9b-b2 heterogeneous-transport design is approved,
and M9b-b2a's action, cochain, and cocycle transport is complete and reviewed.
Endpoint transport and later M9b stages have not started.

## M0 — API audit and foundation decision

- [x] Euclidean-motion API audit completed.
- [x] Lattice API audit completed.
- [x] Multiplication and conjugation prototype compiles.
- [x] Rank-two lattice coordinate prototype compiles.
- [x] Foundation decisions documented.
- [x] Clean `lake build`.

## M1 — Euclidean motions and basic invariants

- [x] Euclidean motion core complete.
- [x] Translation subgroup complete.
- [x] Point group and action complete.
- [x] Normality and exact-sequence API complete.
- [x] Clean `lake build`.

## M2 — Plane groups and equivalence

- [x] Strong plane-group definition complete.
- [x] Translation-preserving isomorphism complete.
- [x] Equivalence relation proved.
- [x] Integral action/basis-change API complete.
- [x] Clean `lake build`.
- [x] Human specification review approved:
      `PlaneGroup` and translation-preserving equivalence.

## M3 — Crystallographic restriction

- [x] Primary proof route selected and documented.
- [x] Rotation orders restricted to `1,2,3,4,6`.
- [x] Orientation-preserving point subgroup shown cyclic.
- [x] Cyclic/dihedral point-group theorem complete.
- [x] Required lattice normal forms complete.
- [x] Clean `lake build`.
- [x] Human specification review approved: crystallographic restriction and lattice normal forms.

## M4 — Five no-reflection classes

- [x] Rotation shift vanishing proved.
- [x] Cyclic extension isomorphism lemma complete.
- [x] `p1 p2 p3 p4 p6` classification complete.
- [x] Clean `lake build`.

## M5 — Three one-reflection classes

- [x] Shift-class API complete.
- [x] Centered/primitive dichotomy complete.
- [x] Reflection quotient computed.
- [x] `cm pm pg` classification complete.
- [x] Clean `lake build`.

## M6 — Nine multiple-reflection classes

- [x] Dihedral generator setup complete.
- [x] `q = 2` four cases complete.
- [x] `q = 3` two cases complete.
- [x] `q = 4` two cases complete.
- [x] `q = 6` one case complete.
- [x] Distinct signatures proved inequivalent.
- [x] Clean `lake build`.

## M7 — Models and main theorem

- [x] All 17 standard models constructed.
- [x] Every model proved to be a plane group.
- [x] Global existence theorem complete.
- [x] Pairwise inequivalence complete.
- [x] Unique classification theorem complete.
- [x] Cardinality corollary complete.
- [x] Clean build from a clean checkout.
- [x] Human specification review approved: final 17-class theorem and standard models.

## M8a — Motion-type equivalence bridge

- [x] Translation, rotation, reflection, and glide-reflection predicates and decomposition validated.
- [x] Textbook-style equivalence proved logically equivalent to `PlaneGroup.Equivalent`.
- [x] Textbook-equivalence 17-class corollary derived without stronger metric or conjugacy assumptions.
- [x] Clean `lake build`.
- [x] Human specification review approved: exact motion-type definitions.

## M8b — Strong plane groups are discrete and cocompact

- [x] Human definition review approved: discreteness and cocompactness notions.
- [x] Exact discreteness and cocompactness notions selected and documented.
- [x] Lattice discreteness and a compact covering set established.
- [x] Every `PlaneGroup` proved discrete and cocompact without new hypotheses.
- [x] Strong-to-geometric conversion applies uniformly to all 17 models.
- [x] Clean `lake build`.
- [x] Human specification review approved: geometric definitions and strong-to-geometric theorem.

## M8c — Discrete cocompact groups yield strong plane groups

- [x] Rank-two full translation lattice and finite point group derived from the geometric hypotheses.
- [x] Human specification review approved: rank-two translation lattice recovery.
- [x] Exact `PlaneGroup` construction, choice independence, and round-trip compatibility proved.
- [x] Unique geometric classification by `WallpaperType` proved with an explicit equivalence relation.
- [x] No hidden lattice or finite-point-group hypothesis and no axiomatized Bieberbach theorem.
- [x] Clean `lake build`.
- [x] Human specification review approved: M8c-c construction and final M8c geometric classification.
- [x] Version 2 M8 geometric bridge complete.

If the project owner explicitly defers M8c as a separate Bieberbach-scale
project, record that decision before starting M9a; do not weaken or mark the
M8c checklist complete.

## M9a — Explicit cocycle extension core

- [x] Explicit actions, normalized cocycles, normalized cochains, coboundaries, and their
      equivalence relation defined without homological group cohomology.
- [x] Normalized-section factors proved normalized and proved to satisfy the cocycle identity.
- [x] Section change proved to be the explicit coboundary formula.
- [x] Twisted-product group, canonical `GroupExtension`, prescribed action, and canonical-section
      recovery constructed.
- [x] Existing point-group extension and dihedral factor connected through thin adapters.
- [x] Version 1 and M8 classification definitions and proofs remain unchanged.
- [x] Clean `lake build`.
- [x] Human specification review approved: explicit cocycle and twisted-extension core.

## M9b — Dimension-independent explicit extension theory

- [x] Coboundary coordinate changes bundled as endpoint-preserving extension equivalences.
- [x] Arbitrary normalized-section extensions reconstructed as equivalent twisted products.
- [x] Cocycle equivalence and endpoint-preserving extension equivalence proved equivalent for
      canonical twisted products.
- [x] M9b-a clean `lake build`.
- [x] Human specification review approved: M9b-a fixed-action extension-equivalence core.
- [x] Normalized-section independence and the arbitrary fixed-action pairwise classifier complete.
- [x] Dimension-independent fixed-action extension-classification theorem completed.
- [x] M9b-b1 clean `lake build`.
- [x] Human specification review approved: M9b-b1 arbitrary fixed-action extension classifier.
- [x] Human design review approved: M9b-b2 heterogeneous extension transport architecture.
- [x] Compatible action equivalences and normalized cochain/cocycle transport implemented.
- [x] Coboundary, `changeBy`, and cohomology naturality plus transport coherence proved.
- [x] M9b-b2a clean `lake build`.
- [x] Human specification review approved: M9b-b2a action and cocycle transport.
- [ ] M9b-b2b extension endpoint transport and heterogeneous equivalence established.
- [ ] M9b-b2c heterogeneous classifier and `TranslationPreservingIso` adapter established.
- [ ] Finite-coset and cyclic `shiftClass` interpretation adapters completed.
- [ ] Core remains independent of plane geometry and supports a thin `T ≅ ℤ^n` specialization.
- [ ] Clean `lake build`.
- [ ] Human specification review approved: final generic extension-classification theorem.
