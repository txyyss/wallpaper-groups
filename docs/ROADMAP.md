# Formalizing the 17 Plane Symmetry Groups in Lean 4

## Codex Roadmap

**Primary target:** a machine-checked classification of the 17 wallpaper groups in Lean 4 + mathlib.

**Primary mathematical reference:** R. L. E. Schwarzenberger, *The 17 plane symmetry groups*.

**Status of this document:** normative project plan. The paper is a mathematical guide, not the formal specification. When this roadmap, the current Lean definitions, and the paper differ, the Lean definitions and explicitly recorded design decisions take precedence.

---

## 0. Codex operating contract

Codex must follow these rules throughout the project.

1. Work on exactly one milestone at a time. Do not begin a later milestone merely because its mathematics looks easier.
2. Before introducing a foundational definition, audit current mathlib. Use `#check`, repository search, source inspection, and small compiling experiments. Do not guess API names from this document.
3. Prefer existing mathlib abstractions when they fit. If a wrapper is needed, keep it thin and prove conversion lemmas immediately.
4. Keep every committed branch buildable with `lake build`.
5. Do not commit `sorry`, `admit`, new axioms, or unproved opaque placeholders. Temporary local experiments may use them only if they are removed before the patch is presented.
6. Keep imports narrow. Do not solve local problems by importing all of Mathlib.
7. Public interfaces should be coordinate-free where practical. Finite classification proofs may use a chosen lattice basis and explicit `2 × 2` matrices internally.
8. Do not make the whole project depend on general group cohomology in version 1. Build a small explicit shift/factor-set API first.
9. Do not define the project around pictures of wallpaper patterns. The classified objects are groups with specified translation subgroups.
10. Record any material deviation from this roadmap in a short design note before implementing it.
11. Each milestone ends with its acceptance checklist, tests, and a brief update to `docs/PROGRESS.md`.
12. When a proof in the paper says “obvious”, “similarly”, or suppresses a compatibility condition, formalize the missing argument explicitly rather than copying the prose.

Recommended first command sequence in an existing repository:

```bash
lake update
lake build
rg "AffineIsometry|LinearIsometry|SemidirectProduct|ZLattice|GroupExtension" .lake/packages/mathlib/Mathlib
```

Adapt the commands to the repository layout. Do not change the Lean toolchain or mathlib revision without an explicit project decision.

---

## 1. Exact theorem being formalized

The first release must classify the same objects and use the same equivalence relation as Schwarzenberger’s elementary proof.

A **plane group** is a subgroup of the Euclidean motion group of `ℝ²` such that:

- its pure translations form a rank-two lattice isomorphic to `ℤ²`; and
- its point group, obtained from the linear part, is finite.

Two plane groups are **equivalent** when there is an abstract group isomorphism between them that maps the translation subgroup onto the translation subgroup.

This is deliberately stronger as input and weaker as equivalence than “conjugate subgroups of the Euclidean isometry group”. It is the right first target because it yields exactly 17 classes without retaining continuous metric parameters such as side lengths and angles.

The main exported type should be:

```lean
inductive WallpaperType
  | p1 | p2 | p3 | p4 | p6
  | cm | pm | pg
  | cmm | pmm | pmg | pgg
  | p3m1 | p31m | p4m | p4g | p6m
  deriving DecidableEq, Fintype
```

The final theorem should have the following mathematical shape:

```lean
noncomputable def WallpaperType.model : WallpaperType → PlaneGroup := ...

 theorem classification (G : PlaneGroup) :
   ∃! w : WallpaperType, PlaneGroup.Equivalent G (WallpaperType.model w)
```

The exact Lean syntax may differ after the API audit. The theorem must imply both:

- existence: every plane group belongs to one of the 17 types;
- uniqueness: no two distinct labels represent equivalent groups.

Only after that theorem is complete should the project add a quotient-level equivalence and a cardinality corollary.

---

## 2. Scope and non-goals

### Version 1 scope

Version 1 includes:

- Euclidean motions of a two-dimensional real inner product space;
- translation subgroup, point group, point-group action, and shift classes;
- the two-dimensional crystallographic restriction;
- classification into `5 + 3 + 9` cases;
- explicit standard models for all 17 classes;
- pairwise inequivalence of the standard models;
- a final classification theorem under translation-preserving abstract group isomorphism.

### Explicit non-goals for version 1

Do not block the classification on any of the following:

- proving from scratch that every discrete cocompact subgroup of `Isom(ℝ²)` has a rank-two translation lattice and finite point group;
- classifying actual wallpaper images, colored patterns, orbifolds, or fundamental-domain drawings;
- proving the full Bieberbach theorems;
- implementing general `H²(H, T)` as the main classification engine;
- formalizing all 17 international crystallographic notations and convention variants;
- proving three-dimensional space-group classifications;
- producing a computable recognizer from an arbitrary finite presentation.

These may be added after the main theorem.

---

## 3. Core mathematical architecture

### 3.1 The Euclidean motion group

Let `E` be a finite-dimensional real inner product space. A Euclidean motion is represented by a pair `(v, A)` with `v : E` and `A` a linear isometry, acting by

```text
x ↦ v + A x.
```

Multiplication is

```text
(v, A) * (w, B) = (v + A w, A * B).
```

Preferred implementation strategy:

- use mathlib’s semidirect product if its API is suitable; or
- use mathlib’s affine isometry equivalence type if it already exposes the required translation and linear-part lemmas cleanly.

Do not maintain two independent primary representations. Pick one in Milestone M0 and provide an equivalence to the other only when useful.

Required API:

```lean
translationPart : EuclideanMotion E → E
linearPart      : EuclideanMotion E →* LinearIsometryGroup E
translation     : E →+ EuclideanMotion E
```

Required lemmas include multiplication, inverse, extensionality, and conjugation of translations:

```text
(v, A) * translation t * (v, A)⁻¹ = translation (A t).
```

This conjugation formula is the main bridge from geometry to the lattice action.

### 3.2 Translation lattice and point group

For a subgroup `G` of Euclidean motions, define:

```text
T(G) = { t : E | translation t ∈ G }
H(G) = image of G under linearPart.
```

Prove:

- `T(G)` is an additive subgroup of `E`;
- the corresponding subgroup of `G` is normal;
- `H(G)` acts on `T(G)`;
- there is a short exact sequence

```text
1 → T(G) → G → H(G) → 1.
```

The project should expose the short exact sequence, but version 1 classification should not require the full general theory of extensions.

### 3.3 Rank-two lattice representation

Milestone M0 must decide whether current mathlib lattice infrastructure is sufficient. The required invariant is:

- an additive subgroup `T ≤ E`;
- an explicit `ℤ`-basis of two elements;
- proof that those basis vectors are linearly independent over `ℝ`.

A robust fallback structure is conceptually:

```lean
structure RankTwoLattice (E : Type*) where
  carrier : AddSubgroup E
  basisEquiv : (Fin 2 → ℤ) ≃+ carrier
  basis_real_linearIndependent :
    LinearIndependent ℝ (fun i => ((basisEquiv (Pi.single i 1) : carrier) : E))
```

This is only a sketch. Reuse a mathlib `ZLattice`, lattice basis, or equivalent abstraction if it provides the same data and usable lemmas.

Do not encode a lattice merely as “two chosen vectors”. The formal object must support unique integer coordinates.

### 3.4 Plane groups

The first concrete definition should package the strong hypotheses directly:

```lean
structure PlaneGroup where
  carrier : Subgroup (EuclideanMotion Plane)
  translationLattice : RankTwoLattice Plane
  translationLattice_carrier :
    translationLattice.carrier = translationVectors carrier
  pointGroup_finite : Finite (pointGroup carrier)
```

Use `Plane := EuclideanSpace ℝ (Fin 2)` unless M0 identifies a materially better existing type.

### 3.5 Equivalence

Define a structure containing a group equivalence and the proof that it carries translations onto translations:

```lean
structure TranslationPreservingIso (G G' : PlaneGroup) where
  toMulEquiv : G.carrier ≃* G'.carrier
  map_translationSubgroup :
    map of G.translationSubgroup = G'.translationSubgroup
```

Then define:

```lean
def PlaneGroup.Equivalent (G G' : PlaneGroup) : Prop :=
  Nonempty (TranslationPreservingIso G G')
```

Prove reflexivity, symmetry, and transitivity before using it in classification statements.

The induced map on the translation lattice must be extracted as a `ℤ`-linear/additive equivalence, and then extended to an `ℝ`-linear equivalence of the plane. Prove that it conjugates the point-group action.

### 3.6 Shift classes, not raw shift vectors

Let `h ∈ H(G)` have finite order `q`, and let `g ∈ G` be a lift of `h`. Then `g^q` is a translation. Its translation vector is fixed by `h`.

Changing the lift changes the vector by the norm map

```text
N_h(t) = t + h t + ... + h^(q - 1) t.
```

Therefore the invariant should be represented by a quotient class

```text
T^h / N_h(T),
```

not by a chosen vector.

For a reflection `h² = 1`, this specializes to

```text
T^h / (1 + h)T.
```

Implement only the API needed by the classification:

- definition of the norm map;
- independence of lift;
- functoriality under translation-preserving isomorphism;
- vanishing for nontrivial rotations;
- classification of the reflection quotient in the relevant rank-two lattice normal forms.

Do not make the entire project depend on a general cohomology package. A later theorem may identify these classes with extension/cohomology data.

---

## 4. Coordinate policy

Use two layers.

### Public layer

Definitions and reusable lemmas should be stated for Euclidean motions, subgroups, lattices, actions, and isomorphisms without unnecessary coordinates.

### Classification layer

After choosing a lattice basis, identify the translation lattice with `ℤ²`. Represent the point-group action by matrices in `GL₂(ℤ)`. Exact matrix normal forms and finite case analysis are permitted and expected here.

Rules:

- all finite calculations must use exact integers, rationals, or algebraic identities;
- do not use floating-point approximations;
- external computer algebra may suggest a proof but may not be trusted as an axiom;
- `native_decide` is acceptable only for genuinely finite decidable propositions after a proved reduction;
- real identities involving `sqrt 3` in standard models require ordinary Lean proofs.

---

## 5. Suggested source tree

Adapt names to the host repository, but preserve the separation of concerns.

```text
WallpaperGroups/
  Basic/
    EuclideanMotion.lean
    RankTwoLattice.lean
    PlaneGroup.lean
    Equivalence.lean
  Invariants/
    PointGroup.lean
    ExactSequence.lean
    ShiftClass.lean
  Restriction/
    Orientation.lean
    Crystallographic.lean
    LatticeNormalForms.lean
  Presentations/
    CyclicExtension.lean
    ReflectionExtension.lean
    DihedralExtension.lean
  Models/
    Common.lean
    RotationModels.lean
    ReflectionModels.lean
    DihedralModels.lean
  Classification/
    NoReflections.lean
    OneReflection.lean
    ManyReflections.lean
    Main.lean
  Geometry/
    DiscreteCocompact.lean       # post-v1
  Cohomology/
    Interpretation.lean         # post-v1
```

Avoid a single large file containing all 17 cases.

---

## 6. Milestones

## M0 — Mathlib API audit and foundation decision

**Goal:** make the foundational representation choices using compiling prototypes rather than assumptions.

### Tasks

1. Inspect current APIs for:
   - affine isometry equivalences;
   - linear isometry equivalences and orthogonal groups;
   - semidirect products;
   - additive subgroups, integer lattices, lattice bases, and discreteness;
   - finite groups and subgroup fintypes;
   - `ZMod`, cyclic groups, and dihedral groups;
   - group extensions and short exact sequences;
   - matrix trace, determinant, characteristic polynomials, and Cayley–Hamilton;
   - quotient additive groups;
   - two-dimensional orientation and rotation APIs.
2. Build two tiny prototypes:
   - composition/conjugation of Euclidean motions;
   - a rank-two lattice with recoverable integer coordinates.
3. Choose one primary Euclidean-motion representation.
4. Choose one primary rank-two-lattice representation.
5. Record the choice in `docs/FOUNDATION_DECISIONS.md` or an equivalent design note.
6. Create the initial namespaces and file skeleton.

### Acceptance criteria

- a small test file compiles and proves the multiplication and translation-conjugation formulas;
- a small test file constructs the standard `ℤ²` lattice and recovers unique integer coordinates;
- no duplicate foundational structure is introduced without a documented reason;
- `lake build` succeeds.

### Stop condition

Do not begin M1 until the two representation decisions are documented and the prototypes compile.

---

## M1 — Euclidean motions and the four basic invariants

**Goal:** formalize the algebraic skeleton used on pages 123–124 of the paper.

In this implementation order, M1 provides the Euclidean-motion core, translation subgroup,
point group, point-group action, normality, and exact-sequence interface.  Although the paper
groups shift vectors with these data, the canonical shift-class, norm-map, and lift-independence
API remains deferred to M5.

### Tasks

1. Define or wrap `EuclideanMotion E`.
2. Prove multiplication, inverse, extensionality, and action-on-points lemmas.
3. Define pure translations and `linearPart`.
4. For a subgroup `G`, define:
   - translation vectors;
   - translation subgroup inside `G`;
   - point group;
   - point-group action on translations.
5. Prove normality of the translation subgroup.
6. Prove the exact-sequence interface.
7. Add simp lemmas sufficient for generator calculations, but avoid global simp rules that loop or erase useful structure.

### Acceptance criteria

The following style of proof should be short and stable:

```lean
example (g : G) (t : G.translationVectors) :
    g * translation t * g⁻¹ = translation (G.pointAction g t) := by
  ...
```

The exact syntax may differ.  The Euclidean-motion core, translation subgroup, point group,
point-group action, and exact-sequence interface must be available to later files.  Shift
classes remain deferred to M5.

---

## M2 — Plane groups and translation-preserving equivalence

**Goal:** formalize the strong definition of plane group and the exact equivalence relation being classified.

### Tasks

1. Implement `RankTwoLattice` or adopt the selected mathlib abstraction.
2. Define `PlaneGroup` with rank-two translations and finite point group.
3. Define `TranslationPreservingIso` and `PlaneGroup.Equivalent`.
4. Prove equivalence-relation laws.
5. Prove that an equivalence induces:
   - an isomorphism of translation lattices;
   - a conjugacy/intertwining relation for point-group actions;
   - preservation of shift classes once they are defined.
6. Prove that the point group is faithfully represented on the lattice.
7. Establish a basis-change API from lattice automorphisms to `GL₂(ℤ)` matrices.

### Acceptance criteria

- the paper’s equivalence notion is represented exactly;
- changing the chosen lattice basis does not change any public invariant;
- a translation-preserving group isomorphism produces the expected matrix conjugacy relation.

---

## M3 — Two-dimensional crystallographic restriction

**Goal:** prove that the orientation-preserving point subgroup has order `1`, `2`, `3`, `4`, or `6`, and obtain the lattice normal forms needed later.

### Required output

A theorem with mathematical content:

```text
rotation order ∈ {1, 2, 3, 4, 6}.
```

Also prove that for orders `3`, `4`, and `6`, a suitable shortest or primitive lattice vector `t` yields a basis of the form `(t, θ t)`.

### Preferred proof route A: trace and Cayley–Hamilton

After choosing a lattice basis, the rotation action is an integer matrix. Its real linear trace is an integer. Since the underlying map is an orientation-preserving isometry of a two-dimensional Euclidean space, its trace lies in `[-2, 2]`. Hence the trace is one of

```text
-2, -1, 0, 1, 2.
```

Use determinant `1` and Cayley–Hamilton to derive orders `2`, `3`, `4`, `6`, and `1` respectively.

This route is preferred if current mathlib provides manageable trace, determinant, and matrix/linear-map conversion lemmas.

### Fallback proof route B: shortest lattice vector

Use the paper’s argument:

- choose a nonzero translation vector of minimum norm;
- compare it with its rotations;
- use the fact that two shortest vectors cannot make too small an angle;
- derive the allowed orders and basis normal forms.

This route requires a clean existence theorem for a shortest nonzero vector in a rank-two lattice.

### Additional point-group theorem

Prove that the orientation-preserving subgroup is cyclic and that any orientation-reversing element conjugates its generator to its inverse. Consequently every finite point group is cyclic or dihedral in the required sense.

### Acceptance criteria

- no analytic approximation of angles;
- an exported finite type or predicate representing `{1,2,3,4,6}`;
- a reusable theorem identifying the point group as cyclic or dihedral;
- basis normal forms needed by M4–M6.

### Decision rule

Prototype both proof routes only long enough to assess API cost. Commit one primary proof. Record the rejected route and reason; do not leave two half-maintained foundations.

---

## M4 — The five classes without reflections

**Goal:** formalize the first classification theorem: `p1`, `p2`, `p3`, `p4`, `p6`.

### Mathematics

If the point group contains no reflections, it is cyclic of order

```text
q ∈ {1, 2, 3, 4, 6}.
```

For a nonidentity rotation, the fixed subspace in the plane is zero. Therefore its shift class vanishes. The group is determined, up to the chosen equivalence, by the lattice action of the cyclic point group.

### Tasks

1. Prove that shift vectors/classes for nontrivial rotations vanish.
2. Package the paper’s coset construction into a reusable cyclic-extension isomorphism lemma.
3. Prove that two reflection-free plane groups with the same rotation order are equivalent.
4. Prove that differing rotation orders imply inequivalence.
5. Define or reserve the five corresponding `WallpaperType` constructors.

### Suggested intermediate theorem

```lean
 theorem classify_no_reflections (G : PlaneGroup)
     (hG : G.pointGroupHasNoReflections) :
   ∃! q : CrystallographicOrder,
     G.Equivalent (rotationModel q)
```

### Acceptance criteria

- exactly five equivalence classes in this subcase;
- no standard-model geometry beyond what is needed for these five;
- the generic cyclic extension lemma is reusable rather than copied five times.

This is the first major vertical slice. Do not proceed until it is complete.

---

## M5 — Shift classes and the three classes with one reflection

**Goal:** formalize `cm`, `pm`, and `pg`.

### Mathematics

When the point group contains exactly one nonidentity reflection, it has order two. Let `ρ` be that reflection. The relevant invariant is

```text
T^ρ / (1 + ρ)T.
```

The lattice action has two normal forms:

- centered rectangular;
- primitive rectangular.

In the centered case the quotient gives the `cm` class. In the primitive case the zero shift gives `pm` and the nonzero parity class gives `pg`.

### Tasks

1. Implement the finite-order norm map and shift class.
2. Prove independence from the chosen lift.
3. Prove functoriality under translation-preserving isomorphism.
4. For a reflection, define the fixed and anti-fixed lattice directions.
5. Prove the centered/primitive lattice dichotomy.
6. Compute the reflection shift quotient in both normal forms.
7. Package the two-coset construction into a reusable reflection-extension isomorphism lemma.
8. Construct and distinguish `cm`, `pm`, and `pg`.

### Acceptance criteria

- the proof does not store a noncanonical raw shift vector as the invariant;
- the primitive mirror/glide distinction is represented as zero versus nonzero quotient class;
- exactly three equivalence classes in this subcase.

---

## M6 — The nine classes with more than one reflection

**Goal:** formalize the dihedral cases and obtain `4 + 2 + 2 + 1 = 9` classes.

### Mathematics

Choose adjacent reflections `ρ` and `σ` such that `θ = ρσ` generates the rotation subgroup. The possible rotation orders are `2`, `3`, `4`, and `6`.

The classification splits as follows:

- `q = 2`: four classes `cmm`, `pmm`, `pmg`, `pgg`;
- `q = 3`: two classes `p3m1`, `p31m`;
- `q = 4`: two classes `p4m`, `p4g`;
- `q = 6`: one class `p6m`.

### Tasks

1. Prove the point group is generated by two reflections with product a rotation generator.
2. Choose compatible primitive lattice vectors on the reflection axes.
3. Prove the lattice normal forms for each `q`.
4. Define the pair of reflection shift classes and prove compatibility imposed by the rotation product.
5. Perform the finite case split:
   - four signatures for `q = 2`;
   - two lattice signatures for `q = 3`;
   - two shift signatures for `q = 4`;
   - one signature for `q = 6`.
6. Prove that exchanging the two reflection generators identifies the two asymmetric `q = 2` descriptions of `pmg`.
7. Package the generator-and-relation argument into a reusable dihedral-extension isomorphism lemma.
8. Prove groups with the same normalized signature are equivalent.
9. Prove distinct normalized signatures are inequivalent.

### Acceptance criteria

- the proof produces exactly nine normalized signatures;
- the `pmg` symmetry under swapping generators is handled explicitly;
- no case is distinguished solely by a drawing or naming convention;
- each signature is characterized by invariant algebraic data.

---

## M7 — Standard models and the global classification theorem

**Goal:** construct all 17 models and combine M4–M6 into the final theorem.

### Standard-model policy

Prefer models with transparent normal forms over subgroups defined only as the closure of generators. Translation-subgroup computations are much easier when every element has a proved unique normal form.

Possible implementation patterns:

1. define an abstract normal-form group (`ℤ²` plus a finite point-group coordinate), then embed it injectively into Euclidean motions; or
2. define a subgroup generated by explicit motions and immediately prove a normal-form theorem strong enough to compute its translations.

Choose one pattern and use it consistently.

### Tasks

1. Construct standard models for all 17 labels.
2. Prove each model is a `PlaneGroup`:
   - translation subgroup is exactly rank two;
   - point group is finite and has the claimed structure.
3. Define an invariant signature for standard models.
4. Prove all 17 signatures are distinct.
5. Combine the three classification theorems.
6. Prove:

```lean
 theorem classification (G : PlaneGroup) :
   ∃! w : WallpaperType, G.Equivalent (WallpaperType.model w)
```

7. Add a quotient-level equivalence only after the theorem above is stable.
8. Derive a cardinality theorem expressing that the classification has 17 classes.

### Naming convention

Use modern short names in the exported enum:

```text
p4m, p4g, p6m
```

The paper uses the longer notations `p4mm`, `p4mg`, and `p6mm`. Mention these as aliases in docstrings, not as separate constructors.

### Acceptance criteria

- all 17 models build without `sorry`;
- every plane group is equivalent to a model;
- distinct labels give inequivalent models;
- the top-level classification file imports only the completed component files;
- `lake build` succeeds from a clean checkout.

---

## M8 — Geometric bridge: discrete and cocompact actions (post-v1)

**Goal:** connect the strong definition used above with the more geometric definition of a wallpaper group.

Define a geometric wallpaper group as a discrete cocompact subgroup of the affine isometry group of the plane, with the exact notion of discreteness/cocompactness chosen from current mathlib topology.

Prove, in two directions where appropriate:

```text
discrete + cocompact
    ⇒ rank-two translation lattice + finite point group,
```

and that every strong plane group acts discretely and cocompactly.

This milestone may require substantial topology, proper discontinuity, compact quotients, or a specialized two-dimensional Bieberbach theorem. It is deliberately excluded from the critical path to the 17-class result.

---

## M9 — Cohomological interpretation and higher-dimensional reuse (post-v1)

**Goal:** explain the classification in the language of extensions without rewriting the completed proof.

Possible outputs:

- identify the shift/factor-set invariant with a class in `H²(H, T)`;
- state a general extension-classification theorem for finite point groups acting on lattices;
- reuse the Euclidean-motion and lattice APIs in higher dimensions;
- separate dimension-independent extension theory from dimension-two case analysis.

Do not start this milestone before M7.

---

## 7. Standard signatures to be represented

The project needs a finite algebraic signature that distinguishes the 17 models. The exact Lean structure is a design choice, but it should encode at least:

- presence or absence of reflections;
- rotation subgroup order;
- integral conjugacy class of the action on `ℤ²`;
- centered versus primitive reflection-lattice form where relevant;
- reflection shift class or normalized pair of shift classes.

A suitable normalized classification table is:

| Family | Rotation order | Additional invariant | Type(s) |
|---|---:|---|---|
| no reflections | 1, 2, 3, 4, 6 | none | `p1 p2 p3 p4 p6` |
| one reflection | 1 | centered; primitive/zero; primitive/nonzero | `cm pm pg` |
| multiple reflections | 2 | centered; primitive shift pairs `00`, `10`, `11` | `cmm pmm pmg pgg` |
| multiple reflections | 3 | two lattice-axis configurations | `p3m1 p31m` |
| multiple reflections | 4 | zero/nonzero normalized reflection shift | `p4m p4g` |
| multiple reflections | 6 | unique | `p6m` |

Do not treat this table as a proof. Every row must be derived from the lattice action and shift-class lemmas.

---

## 8. Reusable proof components to prioritize

The following lemmas should be written generically enough to prevent repeated low-level group calculations.

### 8.1 Cyclic normal-form isomorphism

Given:

- an equivariant isomorphism of translation lattices;
- matching cyclic point-group generators;
- matching generator power/shift data;

construct a translation-preserving group isomorphism.

### 8.2 Reflection normal-form isomorphism

Given:

- an equivariant lattice isomorphism;
- matching reflection action;
- matching reflection shift class;

construct a translation-preserving group isomorphism.

### 8.3 Dihedral normal-form isomorphism

Given:

- an equivariant lattice isomorphism;
- two matched reflection generators;
- matching normalized shift classes and compatibility relations;

construct a translation-preserving group isomorphism.

### 8.4 Invariant preservation

For every `TranslationPreservingIso`, prove preservation of:

- point-group order;
- orientation decomposition;
- lattice action up to integral conjugacy;
- shift classes;
- centered/primitive status;
- normalized signature.

These lemmas are the uniqueness half of the classification.

---

## 9. Testing and proof-quality requirements

Every milestone must include:

1. unit-style examples for standard motions and lattices;
2. theorem-level tests for basis changes;
3. regression tests for multiplication and power formulas;
4. a full `lake build`;
5. no unbounded simp search or fragile proof by accidental simplification;
6. docstrings on exported definitions and theorems;
7. references to the relevant paper section where the mathematical idea originates;
8. an explicit theorem dependency graph in the PR description when a milestone adds more than ten exported results.

Recommended project settings:

```lean
set_option autoImplicit false
```

Use local classical reasoning when needed. Do not mark the entire project `noncomputable` unless necessary; put `noncomputable section` around model choices or basis selections.

When using finite enumeration, separate:

- a human-readable reduction theorem; and
- the final decidable finite check.

The reduction theorem is the mathematical proof. The decision procedure only closes the finite remainder.

---

## 10. Risk register and fallback strategies

### Risk: mathlib affine-isometry API is awkward

Fallback: use a local semidirect-product wrapper as the primary group and prove an equivalence to affine isometries later. Keep the wrapper small.

### Risk: existing lattice abstraction is too general or hard to compute with

Fallback: define a project-local `RankTwoLattice` with explicit `ℤ²` coordinates and prove adapters to mathlib lattice notions later.

### Risk: shortest-vector proof creates a large topology/order-theory detour

Fallback: use the integer-trace/Cayley–Hamilton proof for crystallographic restriction.

### Risk: trace proof needs difficult basis-invariance lemmas

Fallback: use an orthonormal basis to bound the real trace, a lattice basis to prove integrality, and one explicit theorem equating the two traces. If still costly, return to the shortest-vector route.

### Risk: standard models defined by subgroup closure make translation calculations intractable

Fallback: build models from explicit normal-form groups and inject them into Euclidean motions.

### Risk: quotienting by `Equivalent` creates early typeclass and `Fintype` friction

Fallback: keep the main result as unique classification by `WallpaperType`; introduce the quotient only in M7.

### Risk: reflection shift bookkeeping becomes generator-dependent

Fallback: normalize in the quotient `T^ρ / (1 + ρ)T` and prove generator-change lemmas before case splitting.

### Risk: the paper’s notation or OCR is ambiguous

Fallback: use the page images, modern standard names, and explicit standard models. Do not infer formulas from corrupt OCR.

---

## 11. Paper crosswalk

Use `docs/references/Schwarzenberger_17_Plane_Symmetry_Groups.pdf` as follows:

- paper pp. 123–124: Euclidean motions and the four invariants `T`, `H`, the action, and shift vectors;
- pp. 125–126: strong definition of plane group, shortest-vector argument, crystallographic restriction, and reflection shift situations;
- p. 127: equivalence as a group isomorphism carrying `T` onto `T'`;
- pp. 127–128: five no-reflection classes and three one-reflection classes;
- pp. 129–130: nine multiple-reflection classes and the summary table.

Important cautions:

- the first page begins with the end of an unrelated preceding article;
- the last page begins the next article after the relevant references;
- OCR may corrupt Greek letters, fractions, and the table on p. 130;
- the paper uses `p4mm`, `p4mg`, and `p6mm`, while this project exports `p4m`, `p4g`, and `p6m`;
- the paper intentionally omits pictures and compresses several isomorphism arguments;
- the paper assumes the strong rank-two-lattice/finite-point-group definition and does not prove the discrete-cocompact bridge.

The paper is especially useful for the decomposition `5 + 3 + 9` and the generator/coset isomorphism strategy. It should not be translated line by line.

---

## 12. Definition of done for version 1

Version 1 is complete only when all of the following hold:

- `WallpaperType` has exactly 17 constructors and a `Fintype` instance;
- all 17 standard models are defined as plane groups;
- every plane group is equivalent to at least one standard model;
- distinct labels yield inequivalent models;
- the final unique-classification theorem is proved;
- a cardinality corollary is derived;
- no source file contains `sorry`, `admit`, or project-specific axioms;
- the repository builds from a clean checkout;
- the public API has docstrings and a short mathematical overview;
- the README states the exact equivalence relation, so the result is not misrepresented as Euclidean conjugacy classification.

---

## 13. First Codex assignment

Begin with M0 only.

Deliver:

1. an API audit note listing the exact current mathlib declarations selected for Euclidean motions, semidirect products, linear isometries, finite subgroups, lattices, and matrices;
2. a compiling prototype proving the Euclidean-motion multiplication and translation-conjugation formulas;
3. a compiling prototype for a rank-two lattice with unique integer coordinates;
4. a proposed final representation decision with trade-offs;
5. no classification code yet.

Before writing implementation code, summarize the intended patch in no more than ten concrete steps. After implementation, run `lake build` and report every changed file and exported declaration.
