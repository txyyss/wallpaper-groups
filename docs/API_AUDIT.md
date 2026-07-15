# Mathlib API audit

## Scope and reproducibility

This is the M0 audit required by `docs/ROADMAP.md`.  It records APIs that were found in the
locally downloaded mathlib sources and then accepted by Lean; it is not based on guessed names.
The audit was run with:

- Lean and mathlib release: `v4.32.0`;
- Lean commit: `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
- resolved mathlib commit: `81a5d257c8e410db227a6665ed08f64fea08e997`.

The persistent compiling experiments are:

- `WallpaperGroups/Prototype/APIAudit.lean` for representative `#check` commands, finite-range
  transport, a kernel--range group extension, and the integral two-dimensional
  Cayley--Hamilton identity;
- `WallpaperGroups/Prototype/EuclideanMotion.lean` for regression examples against the formal
  Euclidean-motion representation now in `WallpaperGroups/Basic/EuclideanMotion.lean`;
- `WallpaperGroups/Prototype/RankTwoLattice.lean` for the lattice representation, coordinates,
  the standard lattice, and the `GL₂(ℤ)` bridge.

M0-only declarations remain under `WallpaperGroups.Prototype`.  M1 migrated the Euclidean-motion
results to production modules and removed all prototype imports from the public umbrella module.

## Affine isometry equivalences

- **Mathlib module / minimum direct import:**
  `Mathlib.Analysis.Normed.Affine.Isometry`.
- **Checked declarations:** `AffineIsometryEquiv`,
  `AffineIsometryEquiv.linearIsometryEquiv`, `AffineIsometryEquiv.ext`,
  `AffineIsometryEquiv.coe_mul`, `AffineIsometryEquiv.coe_inv`,
  `AffineIsometryEquiv.map_vadd`, `AffineIsometryEquiv.map_vsub`,
  `AffineIsometryEquiv.constVAdd`, `AffineIsometryEquiv.coe_constVAdd`,
  `AffineIsometryEquiv.constVAdd_zero`, `AffineIsometryEquiv.mk'`, and
  `LinearIsometryEquiv.toAffineIsometryEquiv`.
- **Compiling experiment:** `WallpaperGroups/Basic/EuclideanMotion.lean`, the regression examples
  in `WallpaperGroups/Prototype/EuclideanMotion.lean`, and the affine checks in
  `WallpaperGroups/Prototype/APIAudit.lean`.
- **Fit:** excellent as the coordinate-free primary representation.  It already has a group
  structure, an action on points, a canonical linear isometry, and a translation constructor.
- **Gap / risk:** mathlib does not expose a bundled linear-part group homomorphism, a translation
  part, a bundled translation homomorphism, or an equivalence with translation/linear pairs.
  These are thin project lemmas.  Because the target is a multiplicative group, a bundled
  translation homomorphism has type `Multiplicative E →* (E ≃ᵃⁱ[ℝ] E)`, not
  `E →+ (E ≃ᵃⁱ[ℝ] E)`.

## Linear isometries and orthogonal groups

- **Mathlib modules / minimum direct imports:**
  `Mathlib.Analysis.Normed.Operator.LinearIsometry` for coordinate-free linear isometries and
  `Mathlib.LinearAlgebra.UnitaryGroup` for matrix orthogonal groups.
- **Checked declarations:** `LinearIsometryEquiv`, `LinearIsometryEquiv.ext`,
  `LinearIsometryEquiv.toLinearEquiv`, `LinearIsometryEquiv.coe_mul`,
  `LinearIsometryEquiv.coe_inv`, `LinearIsometryEquiv.mul_def`,
  `Matrix.orthogonalGroup`, `Matrix.specialOrthogonalGroup`,
  `Matrix.mem_orthogonalGroup_iff`, `Matrix.mem_specialOrthogonalGroup_iff`, and
  `Matrix.mem_specialOrthogonalGroup_fin_two_iff`.
- **Compiling experiment:** `WallpaperGroups/Basic/EuclideanMotion.lean`,
  `WallpaperGroups/Prototype/EuclideanMotion.lean`, and
  `WallpaperGroups/Prototype/APIAudit.lean`.
- **Fit:** use `E ≃ₗᵢ[ℝ] E` for the coordinate-free linear part.  Matrix orthogonal groups
  are suitable after a basis is chosen, especially for M3.
- **Gap / risk:** there is no separate coordinate-free `OrthogonalGroup` alias and no ready-made
  bundled equivalence from `E ≃ₗᵢ[ℝ] E` to a matrix orthogonal group.  Such a bridge must select
  an orthonormal basis; it should not become the primary representation.

## Semidirect products

- **Mathlib module / minimum direct import:** `Mathlib.GroupTheory.SemidirectProduct`.
- **Checked declarations:** `SemidirectProduct`, `SemidirectProduct.mul_def`,
  `SemidirectProduct.inv_left`, `SemidirectProduct.inv_right`,
  `SemidirectProduct.inl`, `SemidirectProduct.inr`, `SemidirectProduct.inl_aut`,
  `SemidirectProduct.rightHom`, `SemidirectProduct.range_inl_eq_ker_rightHom`,
  `SemidirectProduct.lift`, `SemidirectProduct.map`, and `SemidirectProduct.congr`.
- **Compiling experiment:** the representative check in
  `WallpaperGroups/Prototype/APIAudit.lean`; a disposable compiling probe also constructed
  `Multiplicative E ⋊ (E ≃ₗᵢ[ℝ] E)` and checked its multiplication and conjugation.
- **Fit:** algebraically correct and useful as a comparison object or after a splitting is known.
- **Gap / risk:** vector addition must be retagged as `Multiplicative E`, and the action
  `(E ≃ₗᵢ[ℝ] E) →* MulAut (Multiplicative E)` must be built explicitly.  It does not by itself
  act by affine isometries on points.  This makes it a less direct primary representation than
  `AffineIsometryEquiv`.

## Additive subgroups and integer submodules

- **Mathlib module / minimum direct import:**
  `Mathlib.Algebra.Module.Submodule.Lattice`.
- **Checked declarations:** `AddSubgroup.toIntSubmodule`,
  `AddSubgroup.coe_toIntSubmodule`, `AddSubgroup.toIntSubmodule_toAddSubgroup`,
  `Submodule.toAddSubgroup_toIntSubmodule`, `Submodule.toAddSubgroup`,
  `AddSubgroup.map`, `AddSubgroup.comap`, and `AddMonoidHom.range`.
- **Compiling experiment:** the `AddSubgroup.toIntSubmodule` check in
  `WallpaperGroups/Prototype/APIAudit.lean` and the carrier in
  `WallpaperGroups/Prototype/RankTwoLattice.lean`.
- **Fit:** the order isomorphism between `AddSubgroup E` and `Submodule ℤ E` makes both APIs
  available.  A `Submodule ℤ E` is the better primary carrier because the later coordinate,
  fixed-submodule, norm-map, quotient-module, and matrix APIs are integer-linear.
- **Gap / risk:** a `DiscreteTopology` instance on an `AddSubgroup` does not automatically migrate
  to `toIntSubmodule`; transporting it requires an explicit homeomorphism argument.  Avoid
  crossing this bridge repeatedly.

## Integer lattices, bases, discreteness, and coordinates

- **Mathlib modules / minimum direct imports:**
  `Mathlib.Algebra.Module.ZLattice.Basic` for full lattices and
  `Mathlib.LinearAlgebra.Basis.Submodule` for bases and restricted scalars.
- **Checked declarations:** `IsZLattice`, `IsZLattice.span_top`, `ZLattice.module_finite`,
  `ZLattice.module_free`, `ZLattice.rank`, `Module.Basis.ofZLatticeBasis`,
  `IsZLattice.basis`, `ZLattice.comap`, `ZLattice.comap_equiv`,
  `Module.Basis.ofZLatticeComap`, `Module.Basis.repr`, `Module.Basis.equivFun`,
  `Module.Basis.restrictScalars`, `Module.Basis.restrictScalars_apply`, and
  `Module.Basis.mem_span_iff_repr_mem`.
- **Discreteness declarations checked:** `SetLike.isDiscrete_iff_discreteTopology`,
  `DiscreteTopology.isDiscrete`, and `AddSubgroup.isClosed_of_discrete`.
- **Compiling experiment:** `WallpaperGroups/Prototype/RankTwoLattice.lean` constructs the
  standard span of `Pi.basisFun ℝ (Fin 2)`, obtains its integer basis by
  `Module.Basis.restrictScalars`, synthesizes both `DiscreteTopology` and `IsZLattice`, and proves
  coordinate round trips.
- **Fit:** `Module.Basis (Fin 2) ℤ L` provides exactly the unique coordinate equivalence
  `L ≃ₗ[ℤ] (Fin 2 → ℤ)`.  `IsZLattice ℝ L` is valuable as a derived property for a
  discrete full lattice.
- **Gap / risk:** `IsZLattice` is a proposition requiring `[DiscreteTopology L]` and records full
  real span; it does not carry a chosen basis and is not suitable for lower-rank sublattices.
  `IsZLattice.basis` is specialized to submodules of a function space, so a general Euclidean
  plane needs a transport through coordinates.  The current API spells the basis namespace
  `Module.Basis`; unqualified roadmap names must not be copied blindly.

## Basis matrices and `GL₂(ℤ)`

- **Mathlib modules / minimum direct imports:** `Mathlib.LinearAlgebra.Matrix.Basis` and
  `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`; the prototype uses the convenient
  aggregate `Mathlib.LinearAlgebra.Matrix.ToLin`.
- **Checked declarations:** `Module.Basis.toMatrix`, `Module.Basis.invertibleToMatrix`,
  `LinearMap.toMatrix`, `LinearMap.toMatrix_comp`, `LinearMap.toMatrix_id`,
  `Matrix.GeneralLinearGroup`, `Matrix.GeneralLinearGroup.toLin'`,
  `Matrix.GeneralLinearGroup.det`, and `LinearMap.GeneralLinearGroup.ofLinearEquiv`.
- **Compiling experiment:** `RankTwoLatticeCandidate.automorphismMatrix` and
  `RankTwoLatticeCandidate.automorphismGL` in
  `WallpaperGroups/Prototype/RankTwoLattice.lean`.
- **Fit:** a lattice automorphism can be sent directly to `Matrix.GeneralLinearGroup (Fin 2) ℤ`
  in the chosen basis.  This is the intended internal representation for M2--M3.
- **Gap / risk:** mathlib has no ready classification of finite-order elements of
  `GL₂(ℤ)` suitable for crystallographic restriction; that argument remains project work in M3.

## Finite groups and finite subgroups

- **Mathlib modules / minimum direct imports:** `Mathlib.Algebra.Group.Subgroup.Finite` for
  subtype finiteness, `Mathlib.GroupTheory.Coset.Card` for subgroup cardinality, and
  `Mathlib.GroupTheory.OrderOfElement` for element orders.
- **Checked declarations:** `Subgroup.instFiniteSubtypeMem`, `Fintype.ofFinite`,
  `Finite.of_surjective`, `Subgroup.card_subgroup_dvd_card`, `orderOf_dvd_natCard`, and
  `pow_card_eq_one'`.
- **Compiling experiment:** `WallpaperGroups/Prototype/APIAudit.lean` synthesizes `Finite H` for
  a subgroup and explicitly transports finiteness to a homomorphism range.
- **Fit:** keep `Finite` in theorem statements and use `Fintype.ofFinite` only where enumeration
  is needed.
- **Gap / risk:** `[Finite G]` does not automatically synthesize `Finite f.range`; use
  `Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective`.  `Nat.card` is zero for an
  infinite type, so cardinality arguments must retain explicit finiteness assumptions.

## `ZMod`, cyclic groups, and dihedral groups

- **Mathlib modules / minimum direct imports:** `Mathlib.Data.ZMod.Basic`,
  `Mathlib.GroupTheory.SpecificGroups.Cyclic`, and
  `Mathlib.GroupTheory.SpecificGroups.Dihedral`.
- **Checked declarations:** `ZMod`, `ZMod.card`, `IsCyclic.exists_generator`,
  `zmodAddEquivOfGenerator`, `zmodAddCyclicAddEquiv`, `zmodMulEquivOfGenerator`,
  `zmodCyclicMulEquiv`, `DihedralGroup`, `DihedralGroup.r`, `DihedralGroup.sr`,
  `DihedralGroup.card`, `DihedralGroup.nat_card`, `DihedralGroup.orderOf_r_one`,
  `DihedralGroup.orderOf_sr`, and the four `r`/`sr` multiplication lemmas.
- **Compiling experiment:** the exact types are checked in
  `WallpaperGroups/Prototype/APIAudit.lean`; disposable probes synthesized cyclic and finite
  dihedral instances.
- **Fit:** `Multiplicative (ZMod n)` and `DihedralGroup n` are good standard point-group models.
  `zmodMulEquivOfGenerator` is preferable when a chosen generator must be preserved.
- **Gap / risk:** `ZMod 0` and `DihedralGroup 0` are infinite.  Finite dihedral work must carry
  `[NeZero n]` or equivalent evidence.  There is no `IsDihedral` predicate, arbitrary-group
  recognition theorem, universal property, bundled rotation homomorphism, or ready semidirect
  equivalence.  A local generator/normal-form theorem will be needed later.

## Group extensions and exactness

- **Mathlib modules / minimum direct imports:** `Mathlib.GroupTheory.GroupExtension.Defs` for the
  core extension and `Mathlib.GroupTheory.GroupExtension.Basic` for quotient and splitting
  results.  `Mathlib.Algebra.Exact.Basic` contains the weaker middle-exactness predicate.
- **Checked declarations:** `GroupExtension`, `GroupExtension.inl`,
  `GroupExtension.rightHom`, `GroupExtension.inl_injective`,
  `GroupExtension.range_inl_eq_ker_rightHom`, `GroupExtension.rightHom_surjective`,
  `GroupExtension.conjAct`, `GroupExtension.Equiv`, `GroupExtension.Section`,
  `GroupExtension.Splitting`, `GroupExtension.quotientRangeInlEquivRight`,
  `GroupExtension.Splitting.semidirectProductMulEquiv`, and `Function.MulExact`.
- **Compiling experiment:** `APIAudit.kernelRangeExtension` constructs
  `GroupExtension f.ker E f.range` for every group homomorphism.
- **Fit:** `GroupExtension` exactly packages injection, range equals kernel, and surjection, so it
  is the right base for the M1 translation/point-group exact sequence.
- **Gap / risk:** `GroupExtension.Equiv` fixes both endpoint types, while the project's eventual
  translation-preserving equivalence may change them by isomorphism.  `conjAct` is initially an
  action of the middle group, and descent to the quotient requires a proof.  Splitting results
  apply only to genuinely split extensions; they must not erase glide/reflection shift data.

## Matrices, trace, determinant, characteristic polynomial, and Cayley--Hamilton

- **Mathlib modules / minimum direct imports:** `Mathlib.LinearAlgebra.Matrix.Trace`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, and, for the full M3 route,
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`.
- **Checked declarations:** `Matrix.trace`, `Matrix.trace_fin_two`, `Matrix.trace_mul_comm`,
  `Matrix.det`, `Matrix.det_mul`, `Matrix.det_fin_two_of`, `Matrix.charpoly`,
  `Matrix.charpoly_fin_two`, `Matrix.aeval_self_charpoly`, `Matrix.charpoly_map`,
  `Matrix.trace_eq_neg_charpoly_coeff`, `Matrix.det_eq_sign_charpoly_coeff`,
  `RingHom.map_det`, and `AddMonoidHom.map_trace`.
- **Compiling experiment:** `WallpaperGroups/Prototype/APIAudit.lean` proves over `ℤ`
  `A² - trace(A) A + det(A) I = 0` for every `2 × 2` matrix.
- **Fit:** the explicit `Matrix (Fin 2) (Fin 2) ℤ` layer has all algebraic ingredients for the
  intended M3 trace--determinant--Cayley--Hamilton route.
- **Gap / risk:** Cayley--Hamilton alone does not bound the real trace, identify the determinant
  of an orientation-preserving isometry, or eliminate nontrivial unipotent cases.  Those steps
  must combine this API with orthogonal geometry.  Matrix-first proofs also require an explicit
  conjugacy/basis-change bridge to the real isometry.

## Quotient additive groups and quotient modules

- **Mathlib modules / minimum direct imports:** `Mathlib.GroupTheory.QuotientGroup.Defs` for
  additive quotients and `Mathlib.LinearAlgebra.Quotient.Basic` for integer quotient modules.
- **Checked declarations:** `QuotientAddGroup.mk'`, `QuotientAddGroup.mk'_surjective`,
  `QuotientAddGroup.eq_zero_iff`, `QuotientAddGroup.eq_iff_sub_mem`,
  `QuotientAddGroup.lift`, `QuotientAddGroup.map`, `QuotientAddGroup.congr`,
  `Submodule.Quotient.mk`, `Submodule.mkQ`, `Submodule.liftQ`, `Submodule.mapQ`,
  `Submodule.Quotient.equiv`, and `Submodule.quotEquivOfEq`.
- **Compiling experiment:** representative exact types are checked in
  `WallpaperGroups/Prototype/APIAudit.lean`.
- **Fit:** the future fixed/norm quotient `Tʰ / Nₕ(T)` is better kept as a `ℤ`-quotient module;
  `Submodule.Quotient.equiv` can descend basis-changing equivalences.
- **Gap / risk:** mathlib has no crystallographic norm-map/fixed-quotient bundle.  The project
  will need a thin local definition and lift-independence lemmas in later milestones.

## Two-dimensional orientation, rotations, and reflections

- **Mathlib modules / minimum direct imports:** `Mathlib.LinearAlgebra.Orientation`,
  `Mathlib.Analysis.InnerProductSpace.TwoDim`,
  `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation`,
  `Mathlib.Analysis.InnerProductSpace.Projection.Reflection`, and
  `Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional` for determinant/generation
  results.  Affine-subspace reflection is in `Mathlib.Geometry.Euclidean.Projection`.
- **Checked declarations:** `Module.Basis.orientation`, `Orientation.map`,
  `Orientation.map_eq_iff_det_pos`, `Orientation.rightAngleRotation`,
  `Orientation.areaForm`, `Orientation.rotation`, `Orientation.rotation_apply`,
  `Orientation.det_rotation`, `Orientation.rotation_symm`, `Orientation.rotation_trans`,
  `Orientation.exists_linearIsometryEquiv_eq_of_det_pos`, `Submodule.reflection`,
  `Submodule.reflection_apply`, `Submodule.reflection_mul_reflection`,
  `Submodule.det_reflection`, `LinearIsometryEquiv.reflections_generate`, and
  `EuclideanGeometry.reflection`.
- **Compiling experiment:** the rotation and reflection constructors are checked in
  `WallpaperGroups/Prototype/APIAudit.lean`; a disposable two-dimensional probe constructed the
  standard orientation, a rotation, and an axis reflection and verified determinant/square
  facts.
- **Fit:** the coordinate-free APIs are strong enough for M3's rotation/reflection split and can
  later be connected to selected lattice coordinates.
- **Gap / risk:** there is no bundled orientation-sign homomorphism or ready theorem saying that
  every determinant-negative two-dimensional isometry is one fixed reflection times a rotation.
  The ingredients exist, but the project must provide the thin theorem.  The algebraic,
  inner-product, and affine reflection APIs are separate and should not be conflated.

## Audit outcome

No audited area blocks the roadmap.  The principal API risks are localized: thin parts maps for
affine isometries, basis transport for lattices, finite-range instance transport, arbitrary-group
dihedral recognition, and a few two-dimensional orientation/reflection bridge lemmas.  None
requires replacing mathlib foundations or introducing general group cohomology.

## M1 implementation supplement

M1 rechecked the subgroup, action, and exactness APIs while migrating the Euclidean-motion
prototype into production modules.  The following choices compile at the pinned revisions above.

### Kernels, ranges, and subgroup restrictions

- **Mathlib module / minimum direct import:** `Mathlib.Algebra.Group.Subgroup.Ker`.  Production
  code obtains it transitively through `WallpaperGroups.Basic.EuclideanMotion`; the invariants
  file's only direct project import is that core module.
- **Declarations used:** `MonoidHom.comp`, `MonoidHom.ker`, `MonoidHom.range`,
  `MonoidHom.rangeRestrict`, `MonoidHom.rangeRestrict_surjective`,
  `MonoidHom.ker_rangeRestrict`, `Subgroup.subtype`, `Subgroup.subtype_injective`, and
  `Subgroup.range_subtype`.
- **Compiling files:** `WallpaperGroups/Invariants/Translation.lean` and
  `WallpaperGroups/Invariants/PointGroup.lean`.
- **Fit:** `restrictedLinearPart G := linearPart.comp G.subtype` supports both constructions
  directly.  Its kernel is the translation subgroup; its range is the point group; and
  `rangeRestrict` is the canonical surjection onto that range without changing the kernel.
- **Gap / risk:** subtype coercions create two layers for elements of the kernel subgroup.  The
  project therefore exports named coercion and membership lemmas instead of asking later proofs
  to repeatedly unfold `Subgroup.ker` and `MonoidHom.range`.

### Normal subgroups

- **Mathlib module / minimum direct import:** `Mathlib.Algebra.Group.Subgroup.Ker`.
- **Declaration used:** `MonoidHom.normal_ker`, exposed through the normal instance on a kernel.
- **Compiling files:** `WallpaperGroups/Invariants/Translation.lean` and
  `WallpaperGroups/Invariants/ExactSequence.lean`.
- **Fit:** defining `translationSubgroup G` as `(restrictedLinearPart G).ker` makes normality an
  immediate structural fact rather than a repeated conjugation calculation.  A separate
  geometric conjugation theorem remains available for calculations.
- **Gap / risk:** none for M1.  No rank, discreteness, or lattice assumptions are involved.

### Point-group action on translations

- **Mathlib module / minimum direct import:** `Mathlib.Algebra.Group.End` for `AddAut` and its
  composition law; the production file directly imports the preceding project invariants module.
- **Declarations used:** `AddAut`, `AddEquiv.ext`, `Multiplicative`, and the ordinary additive-map
  laws of `LinearIsometryEquiv`.
- **Compiling file:** `WallpaperGroups/Invariants/PointGroup.lean`.
- **Fit:** `pointAction G h` is an explicit `AddAut (translationVectors G)`.  Closure is proved by
  taking the range witness for `h`, applying the motion conjugation formula, and using subgroup
  closure.  The bundled composition map is
  `pointActionHom G : pointGroup G →* Multiplicative (AddAut (translationVectors G))`.
- **Gap / risk:** in current mathlib, `AddAut A` is deliberately an additive group whose addition
  denotes composition.  Consequently `pointGroup G →* AddAut A` is not a well-typed multiplicative
  homomorphism; the `Multiplicative` tag is required.  M1 uses an explicit action rather than
  installing a global `DistribMulAction`, keeping typeclass search and future lattice adapters
  local and predictable.

### Exact-sequence interface

- **Mathlib module / minimum direct import:** `Mathlib.GroupTheory.GroupExtension.Defs`.
- **Declarations used:** `GroupExtension` and its fields `inl`, `rightHom`, `inl_injective`,
  `range_inl_eq_ker_rightHom`, and `rightHom_surjective`; also `GroupExtension.conjAct` and
  `GroupExtension.inl_conjAct_comm`.
- **Compiling file:** `WallpaperGroups/Invariants/ExactSequence.lean`.
- **Fit:** `pointGroupExtension G` packages exactly
  `1 → translationSubgroup G → G → pointGroup G → 1`.  The file also exports each injectivity,
  surjectivity, and range--kernel fact separately, plus a theorem identifying the extension's
  abstract conjugation action with the geometric point action.
- **Gap / risk:** `GroupExtension.Equiv` fixes the endpoint types, so M2's equivalences between
  different plane groups may still need endpoint transport.  M1 does not import
  `GroupExtension.Basic`, category-theoretic short exact sequences, or general extension
  classification; none is needed for the exactness facts above.

### Production import graph

The stable M1 graph is intentionally narrow:

```text
Mathlib.Analysis.Normed.Affine.Isometry
  → WallpaperGroups.Basic.EuclideanMotion
  → WallpaperGroups.Invariants.Translation
  → WallpaperGroups.Invariants.PointGroup
  → WallpaperGroups.Invariants.ExactSequence
      + Mathlib.GroupTheory.GroupExtension.Defs
```

`WallpaperGroups.Prototype.APIAudit` is no longer imported by the public umbrella module.
