import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
import WallpaperGroups.Geometry.GeometricWallpaperGroup
import WallpaperGroups.Geometry.MotionType
import WallpaperGroups.Restriction.Orientation

set_option linter.style.header false

/-!
# Recovering finite point groups from geometric wallpaper groups

This module implements the first stage of the converse geometric bridge.  It develops
orientation helpers for the point group of an arbitrary plane-motion subgroup and uses proper
discontinuity plus cocompactness to prove that its point group is finite.  The pure-translation
subgroup consequently has finite index.

The final section packages an already-discrete full-rank integer submodule as the project's
`RankTwoLattice`.  Its chosen integer basis is deliberately noncanonical; only the unchanged
carrier is exposed as a stable fact.  Recovering the full-rank translation lattice and
constructing a `PlaneGroup` are deferred to later M8c stages.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion
open scoped RealInnerProductSpace

noncomputable section

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨Plane.finrank⟩

namespace MotionSubgroup

/-! ## Subgroup-level orientation -/

/-- The determinant homomorphism on the point group of an arbitrary plane-motion subgroup. -/
def pointGroupDet (Γ : Subgroup (EuclideanMotion Plane)) :
    pointGroup Γ →* ℝˣ :=
  LinearEquiv.det.comp
    (linearIsometryToLinearEquiv.comp (pointGroup Γ).subtype)

/-- Evaluating the subgroup-level determinant homomorphism gives the ordinary real determinant. -/
@[simp]
theorem pointGroupDet_apply (Γ : Subgroup (EuclideanMotion Plane))
    (A : pointGroup Γ) :
    ((pointGroupDet Γ A : ℝˣ) : ℝ) =
      LinearMap.det
        ((A : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) := by
  simp [pointGroupDet, linearIsometryToLinearEquiv]
  rfl

/--
The positive-determinant subgroup of the point group of an arbitrary plane-motion subgroup.
-/
def orientationPreservingPointGroup
    (Γ : Subgroup (EuclideanMotion Plane)) : Subgroup (pointGroup Γ) where
  carrier := {A | 0 < ((pointGroupDet Γ A : ℝˣ) : ℝ)}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one, Units.val_one]
    positivity
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_ofPred_eq] at hA hB ⊢
    change 0 < ((pointGroupDet Γ (A * B) : ℝˣ) : ℝ)
    rw [map_mul]
    exact mul_pos hA hB
  inv_mem' := by
    intro A hA
    simp only [Set.mem_ofPred_eq] at hA ⊢
    change 0 < ((pointGroupDet Γ A⁻¹ : ℝˣ) : ℝ)
    rw [map_inv]
    simpa only [Units.val_inv_eq_inv_val] using inv_pos.mpr hA

/--
The subgroup-level determinant specializes definitionally to the approved `PlaneGroup`
determinant.
-/
@[simp]
theorem pointGroupDet_planeGroup (G : PlaneGroup) :
    pointGroupDet G.carrier = WallpaperGroups.pointGroupDet G :=
  rfl

/--
The subgroup-level positive point group specializes definitionally to the approved M3 subgroup.
-/
@[simp]
theorem orientationPreservingPointGroup_planeGroup (G : PlaneGroup) :
    orientationPreservingPointGroup G.carrier =
      WallpaperGroups.orientationPreservingPointGroup G :=
  rfl

/-- Membership in the subgroup-level positive point group is positivity of the real determinant. -/
@[simp]
theorem mem_orientationPreservingPointGroup_iff
    (Γ : Subgroup (EuclideanMotion Plane)) (A : pointGroup Γ) :
    A ∈ orientationPreservingPointGroup Γ ↔
      0 < LinearMap.det
        ((A : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) := by
  simp [orientationPreservingPointGroup]

/-- Determinant is multiplicative on plane linear isometries. -/
private theorem linearIsometry_det_mul (f g : Plane ≃ₗᵢ[ℝ] Plane) :
    LinearMap.det
        ((f * g).toLinearEquiv : Plane →ₗ[ℝ] Plane) =
      LinearMap.det (f.toLinearEquiv : Plane →ₗ[ℝ] Plane) *
        LinearMap.det (g.toLinearEquiv : Plane →ₗ[ℝ] Plane) := by
  rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.toLinearEquiv_trans]
  change
    LinearMap.det
        ((f.toLinearEquiv : Plane →ₗ[ℝ] Plane) ∘ₗ
          (g.toLinearEquiv : Plane →ₗ[ℝ] Plane)) = _
  rw [LinearMap.det_comp]

/-- Two positive-determinant linear isometries of the oriented plane commute. -/
private theorem positive_linearIsometries_commute
    (f g : Plane ≃ₗᵢ[ℝ] Plane)
    (hf : 0 < LinearMap.det (f.toLinearEquiv : Plane →ₗ[ℝ] Plane))
    (hg : 0 < LinearMap.det (g.toLinearEquiv : Plane →ₗ[ℝ] Plane)) :
    f * g = g * f := by
  obtain ⟨θ, rfl⟩ :=
    planeOrientation.exists_linearIsometryEquiv_eq_of_det_pos hf
  obtain ⟨φ, rfl⟩ :=
    planeOrientation.exists_linearIsometryEquiv_eq_of_det_pos hg
  apply LinearIsometryEquiv.ext
  intro x
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply,
    planeOrientation.rotation_rotation]
  rw [add_comm]

/-- Conjugating a positive plane isometry by another positive one leaves it unchanged. -/
private theorem positive_conjugates_positive_to_self
    (f g : Plane ≃ₗᵢ[ℝ] Plane)
    (hf : 0 < LinearMap.det (f.toLinearEquiv : Plane →ₗ[ℝ] Plane))
    (hg : 0 < LinearMap.det (g.toLinearEquiv : Plane →ₗ[ℝ] Plane)) :
    f * g * f⁻¹ = g := by
  rw [positive_linearIsometries_commute f g hf hg]
  simp

/-! ## Compact-set finiteness -/

/--
Only finitely many elements of a geometrically discrete motion subgroup move one compact set to
meet another compact set.
-/
theorem compact_intersections_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : IsDiscrete Γ) {K L : Set Plane}
    (hK : IsCompact K) (hL : IsCompact L) :
    {γ : Γ | ((γ • ·) '' K ∩ L).Nonempty}.Finite :=
  (isDiscrete_iff_compact_finite Γ).mp hdisc hK hL

/--
Only finitely many elements of a geometrically discrete motion subgroup fix some point of a
given compact set.
-/
theorem fixedPoint_in_compact_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : IsDiscrete Γ) {K : Set Plane} (hK : IsCompact K) :
    {γ : Γ | ∃ x ∈ K, γ • x = x}.Finite := by
  apply (compact_intersections_finite Γ hdisc hK hK).subset
  rintro γ ⟨x, hxK, hγx⟩
  exact ⟨x, ⟨x, hxK, hγx⟩, hxK⟩

/-! ## Finite point group -/

/--
The positive-determinant part of the point group of a discrete cocompact plane-motion subgroup
is finite.

Every nonidentity positive point element has a rotational lift with a fixed point.  Move that
point into a compact orbit-representative set and conjugate the lift.  Proper discontinuity gives
only finitely many such conjugates, while the conjugated linear part is the original point
element or its inverse according to the conjugator's determinant sign.
-/
theorem orientationPreservingPointGroup_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : IsDiscrete Γ) (hcoc : IsCocompact Γ) :
    Finite (orientationPreservingPointGroup Γ) := by
  classical
  rw [isCocompact_iff_exists_compact_orbit_representatives] at hcoc
  obtain ⟨K, hK, hrepresentatives⟩ := hcoc
  let fixedInK : Set Γ := {q | ∃ x ∈ K, q • x = x}
  have hfixedInK : fixedInK.Finite :=
    fixedPoint_in_compact_finite Γ hdisc hK
  let projected : Set (pointGroup Γ) := pointProjection Γ '' fixedInK
  have hprojected : projected.Finite :=
    hfixedInK.image (pointProjection Γ)
  let projectedInv : Set (pointGroup Γ) :=
    (fun A => A⁻¹) '' projected
  have hprojectedInv : projectedInv.Finite :=
    hprojected.image fun A => A⁻¹
  apply Set.finite_coe_iff.mpr
  refine ((hprojected.union hprojectedInv).insert 1).subset ?_
  intro A hA
  by_cases hAone : A = 1
  · simp [hAone]
  obtain ⟨g, hg⟩ := pointGroup_exists_lift Γ A
  have hgproj : pointProjection Γ g = A :=
    Subtype.ext hg
  have hAdet :
      0 < LinearMap.det
        ((A : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) :=
    (mem_orientationPreservingPointGroup_iff Γ A).mp hA
  have hgrot : PlaneMotion.IsRotation (g : EuclideanMotion Plane) := by
    constructor
    · simpa [PlaneMotion.determinant, hg] using hAdet
    · intro htranslation
      apply hAone
      apply Subtype.ext
      simpa [PlaneMotion.IsTranslation, hg] using htranslation
  obtain ⟨x, hx⟩ := PlaneMotion.isRotation_hasFixedPoint hgrot
  obtain ⟨h, hyK⟩ := hrepresentatives x
  let y : Plane := h • x
  let q : Γ := h * g * h⁻¹
  have hqy : q • y = y := by
    calc
      q • y = h • (g • (h⁻¹ • (h • x))) := rfl
      _ = h • (g • x) := by rw [inv_smul_smul]
      _ = h • x := by
        change
          (h : EuclideanMotion Plane) ((g : EuclideanMotion Plane) x) =
            (h : EuclideanMotion Plane) x
        rw [hx]
      _ = y := rfl
  have hqfixed : q ∈ fixedInK :=
    ⟨y, hyK, hqy⟩
  have hqprojected : pointProjection Γ q ∈ projected :=
    ⟨q, hqfixed, rfl⟩
  have hqproj :
      pointProjection Γ q =
        pointProjection Γ h * A * (pointProjection Γ h)⁻¹ := by
    simp [q, hgproj]
  rcases lt_or_gt_of_ne
      (PlaneMotion.determinant_ne_zero (h : EuclideanMotion Plane)) with
    hneg | hpos
  · have hconj :=
      negative_conjugates_positive_to_inverse
        (linearPart (h : EuclideanMotion Plane))
        (A : Plane ≃ₗᵢ[ℝ] Plane) hneg hAdet
    have hqeq : pointProjection Γ q = A⁻¹ := by
      rw [hqproj]
      apply Subtype.ext
      exact hconj
    refine Set.mem_insert_iff.mpr
      (Or.inr (Set.mem_union _ _ _ |>.mpr (Or.inr ?_)))
    refine ⟨A⁻¹, ?_, by simp⟩
    simpa [hqeq] using hqprojected
  · have hconj :=
      positive_conjugates_positive_to_self
        (linearPart (h : EuclideanMotion Plane))
        (A : Plane ≃ₗᵢ[ℝ] Plane) hpos hAdet
    have hqeq : pointProjection Γ q = A := by
      rw [hqproj]
      apply Subtype.ext
      exact hconj
    refine Set.mem_insert_iff.mpr
      (Or.inr (Set.mem_union _ _ _ |>.mpr (Or.inl ?_)))
    simpa [hqeq] using hqprojected

/--
The point group of a discrete cocompact plane-motion subgroup is finite.

The positive part is finite by the compact rotation-center argument.  If a negative element
exists, left multiplication by one such element injects the negative part into the positive
part.
-/
theorem pointGroup_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : IsDiscrete Γ) (hcoc : IsCocompact Γ) :
    Finite (pointGroup Γ) := by
  classical
  let positive : Set (pointGroup Γ) :=
    orientationPreservingPointGroup Γ
  let negative : Set (pointGroup Γ) :=
    {A |
      LinearMap.det
        ((A : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) < 0}
  have hpositive : positive.Finite := by
    let _ : Finite (orientationPreservingPointGroup Γ) :=
      orientationPreservingPointGroup_finite Γ hdisc hcoc
    exact Set.toFinite positive
  have hnegative : negative.Finite := by
    by_cases hnonempty : negative.Nonempty
    · obtain ⟨s, hs⟩ := hnonempty
      let f : pointGroup Γ → pointGroup Γ := fun A => s * A
      apply Set.Finite.of_finite_image (f := f)
      · apply hpositive.subset
        rintro A ⟨B, hB, rfl⟩
        change s * B ∈ orientationPreservingPointGroup Γ
        rw [mem_orientationPreservingPointGroup_iff, Subgroup.coe_mul]
        rw [linearIsometry_det_mul]
        exact mul_pos_of_neg_of_neg hs hB
      · intro A _ B _ hAB
        exact mul_left_cancel hAB
    · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty]
      exact Set.finite_empty
  apply Finite.of_finite_univ
  apply (hpositive.union hnegative).subset
  intro A _
  have hne :
      LinearMap.det
          (((A : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv) :
            Plane →ₗ[ℝ] Plane) ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    exact hneg
  · left
    exact (mem_orientationPreservingPointGroup_iff Γ A).mpr hpos

/-- Finite point group implies that the full pure-translation subgroup has finite index. -/
theorem translationSubgroup_finiteIndex
    (Γ : Subgroup (EuclideanMotion Plane))
    [Finite (pointGroup Γ)] :
    (translationSubgroup Γ).FiniteIndex := by
  rw [← pointProjection_ker]
  infer_instance

/--
The full pure-translation subgroup of a discrete cocompact plane-motion subgroup has finite
index.
-/
theorem translationSubgroup_finiteIndex_of_geometric
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : IsDiscrete Γ) (hcoc : IsCocompact Γ) :
    (translationSubgroup Γ).FiniteIndex := by
  let _ : Finite (pointGroup Γ) :=
    pointGroup_finite Γ hdisc hcoc
  exact translationSubgroup_finiteIndex Γ

end MotionSubgroup

namespace GeometricWallpaperGroup

/-- The point group of every geometric wallpaper group is finite. -/
instance pointGroupFinite (X : GeometricWallpaperGroup) :
    Finite (pointGroup X.carrier) :=
  MotionSubgroup.pointGroup_finite X.carrier X.isDiscrete X.isCocompact

/-- The full pure-translation subgroup of a geometric wallpaper group has finite index. -/
instance translationSubgroupFiniteIndex (X : GeometricWallpaperGroup) :
    (translationSubgroup X.carrier).FiniteIndex :=
  MotionSubgroup.translationSubgroup_finiteIndex X.carrier

end GeometricWallpaperGroup

namespace RankTwoLattice

/-! ## Adapter from mathlib integer lattices -/

/--
Package a discrete full-rank integer submodule of the plane as a `RankTwoLattice`.

The chosen `Fin 2` basis is noncanonical computational framing data.  Consumers must use the
carrier theorem below, rather than the selected basis, for basis-independent public invariants.
-/
def ofZLattice
    (L : Submodule ℤ Plane) [DiscreteTopology L] [IsZLattice ℝ L] :
    RankTwoLattice Plane := by
  letI : Module.Finite ℤ L :=
    ZLattice.module_finite ℝ L
  letI : Module.Free ℤ L :=
    ZLattice.module_free ℝ L
  let b₀ := Module.Free.chooseBasis ℤ L
  let e : Module.Free.ChooseBasisIndex ℤ L ≃ Fin 2 :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex,
        ZLattice.rank ℝ L, Plane.finrank]
      simp)
  let b : Module.Basis (Fin 2) ℤ L :=
    b₀.reindex e
  exact
    { carrier := L
      basis := b
      basis_real_linearIndependent := by
        have h := (b.ofZLatticeBasis ℝ L).linearIndependent
        have heq :
            (fun i => (b i : Plane)) =
              (fun i => b.ofZLatticeBasis ℝ L i) := by
          funext i
          exact (b.ofZLatticeBasis_apply ℝ L i).symm
        rw [heq]
        exact h }

/-- The lattice adapter does not change the underlying integer submodule. -/
@[simp]
theorem ofZLattice_carrier
    (L : Submodule ℤ Plane) [DiscreteTopology L] [IsZLattice ℝ L] :
    (ofZLattice L).carrier = L :=
  rfl

end RankTwoLattice

end

end WallpaperGroups
