import Mathlib.Topology.Algebra.ConstMulAction
import WallpaperGroups.Basic.EuclideanMotion
import WallpaperGroups.Basic.Plane

set_option linter.style.header false

/-!
# Geometric wallpaper groups

This module equips every subgroup of plane Euclidean motions with its evaluation action and fixes
the geometric definitions used by the Version 2 bridge.  Discreteness means proper discontinuity
in the compact-set finite-intersection sense.  Cocompactness is witnessed by a compact set whose
translates cover the plane.
-/

set_option autoImplicit false

namespace WallpaperGroups

open Filter
open scoped Topology

noncomputable section

/-- A subgroup of Euclidean motions acts on the plane by evaluation. -/
instance motionSubgroupMulAction (Γ : Subgroup (EuclideanMotion Plane)) :
    MulAction Γ Plane where
  smul g x := (g : EuclideanMotion Plane) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Every individual Euclidean motion in a subgroup acts continuously on the plane. -/
instance motionSubgroupContinuousConstSMul (Γ : Subgroup (EuclideanMotion Plane)) :
    ContinuousConstSMul Γ Plane where
  continuous_const_smul g := (g : EuclideanMotion Plane).continuous

namespace MotionSubgroup

/--
Geometric discreteness of a Euclidean-motion subgroup: its evaluation action is properly
discontinuous, in the compact-set finite-intersection sense.
-/
def IsDiscrete (Γ : Subgroup (EuclideanMotion Plane)) : Prop :=
  ProperlyDiscontinuousSMul Γ Plane

/--
Cocompactness of a Euclidean-motion subgroup: some compact subset of the plane has translates
covering the whole plane.
-/
def IsCocompact (Γ : Subgroup (EuclideanMotion Plane)) : Prop :=
  ∃ K : Set Plane, IsCompact K ∧ ⋃ γ : Γ, (γ • ·) '' K = Set.univ

/-- The orbit space of a Euclidean-motion subgroup acting on the plane. -/
abbrev OrbitSpace (Γ : Subgroup (EuclideanMotion Plane)) :=
  MulAction.orbitRel.Quotient Γ Plane

/-- The selected discreteness notion is exactly mathlib's compact-set finiteness condition. -/
theorem isDiscrete_iff_compact_finite (Γ : Subgroup (EuclideanMotion Plane)) :
    IsDiscrete Γ ↔
      ∀ {K L : Set Plane}, IsCompact K → IsCompact L →
        {γ : Γ | ((γ • ·) '' K ∩ L).Nonempty}.Finite :=
  properlyDiscontinuousSMul_iff

/--
The translate-cover formulation of cocompactness is equivalent to requiring every orbit to meet
one compact set.
-/
theorem isCocompact_iff_exists_compact_orbit_representatives
    (Γ : Subgroup (EuclideanMotion Plane)) :
    IsCocompact Γ ↔
      ∃ K : Set Plane, IsCompact K ∧ ∀ x : Plane, ∃ γ : Γ, γ • x ∈ K := by
  constructor
  · rintro ⟨K, hK, hcover⟩
    refine ⟨K, hK, fun x => ?_⟩
    have hx : x ∈ ⋃ γ : Γ, (γ • ·) '' K := by
      rw [hcover]
      trivial
    simp only [Set.mem_iUnion] at hx
    obtain ⟨γ, y, hyK, hγy⟩ := hx
    refine ⟨γ⁻¹, ?_⟩
    rw [← show γ • y = x from hγy]
    simpa using hyK
  · rintro ⟨K, hK, hrepresentatives⟩
    refine ⟨K, hK, Set.eq_univ_of_forall ?_⟩
    intro x
    obtain ⟨γ, hγxK⟩ := hrepresentatives x
    exact Set.mem_iUnion_of_mem γ⁻¹ ⟨γ • x, hγxK, by simp⟩

/-- A compact covering set makes the orbit space compact. -/
theorem IsCocompact.compact_orbitSpace {Γ : Subgroup (EuclideanMotion Plane)}
    (hΓ : IsCocompact Γ) :
    CompactSpace (OrbitSpace Γ) := by
  rcases hΓ with ⟨K, hK, hcover⟩
  letI := MulAction.orbitRel Γ Plane
  refine ⟨?_⟩
  have hpreimage :
      Quotient.mk' ⁻¹' (Quotient.mk' '' K) = Set.univ := by
    rw [MulAction.quotient_preimage_image_eq_union_mul, hcover]
  have himage : Quotient.mk' '' K = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨x, rfl⟩ := Quotient.mk'_surjective z
    have hx : x ∈ Quotient.mk' ⁻¹' (Quotient.mk' '' K) := by
      rw [hpreimage]
      exact Set.mem_univ x
    exact hx
  rw [← himage]
  exact hK.image continuous_quotient_mk'

/-- A compact orbit space admits a compact covering set in the plane. -/
theorem isCocompact_of_compact_orbitSpace {Γ : Subgroup (EuclideanMotion Plane)}
    (hΓ : CompactSpace (OrbitSpace Γ)) :
    IsCocompact Γ := by
  rw [isCocompact_iff_exists_compact_orbit_representatives]
  letI := MulAction.orbitRel Γ Plane
  let Q := OrbitSpace Γ
  letI : CompactSpace Q := hΓ
  let q : Plane → Q := Quotient.mk''
  let representative : Q → Plane := Quotient.out
  choose K hKcompact hKneighborhood using
    fun z : Q => exists_compact_mem_nhds (representative z)
  let U : Q → Set Q := fun z => q '' K z
  have hU_neighborhood (z : Q) : U z ∈ 𝓝 z := by
    have himage : q '' K z ∈ 𝓝 (q (representative z)) :=
      MulAction.isOpenQuotientMap_quotientMk.isOpenMap.image_mem_nhds
        (hKneighborhood z)
    simpa [U, q, representative] using himage
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU_neighborhood
  refine ⟨⋃ z ∈ t, K z, t.isCompact_biUnion fun z _ => hKcompact z, ?_⟩
  intro x
  have hqx : q x ∈ ⋃ z ∈ t, U z := by
    rw [ht]
    trivial
  simp only [Set.mem_iUnion] at hqx
  obtain ⟨z, hz⟩ := hqx
  obtain ⟨hzmem, hqK⟩ := hz
  obtain ⟨y, hyK, hqyx⟩ := hqK
  have horbit : MulAction.orbitRel Γ Plane y x := by
    apply Quotient.exact
    exact hqyx
  rw [MulAction.orbitRel_apply] at horbit
  obtain ⟨γ, hγ⟩ := horbit
  refine ⟨γ, ?_⟩
  rw [show γ • x = y from hγ]
  exact Set.mem_iUnion_of_mem z (Set.mem_iUnion_of_mem hzmem hyK)

/--
For Euclidean-motion subgroups of the plane, the selected compact-cover definition of
cocompactness is equivalent to compactness of the orbit quotient.
-/
theorem isCocompact_iff_compact_orbitSpace
    (Γ : Subgroup (EuclideanMotion Plane)) :
    IsCocompact Γ ↔ CompactSpace (OrbitSpace Γ) :=
  ⟨IsCocompact.compact_orbitSpace, isCocompact_of_compact_orbitSpace⟩

end MotionSubgroup

/--
A geometric wallpaper group is a Euclidean-motion subgroup whose plane action is properly
discontinuous and cocompact.
-/
structure GeometricWallpaperGroup where
  carrier : Subgroup (EuclideanMotion Plane)
  isDiscrete : MotionSubgroup.IsDiscrete carrier
  isCocompact : MotionSubgroup.IsCocompact carrier

end

end WallpaperGroups
