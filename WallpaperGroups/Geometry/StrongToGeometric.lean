import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
import WallpaperGroups.Basic.PlaneGroup
import WallpaperGroups.Geometry.GeometricWallpaperGroup
import WallpaperGroups.Restriction.LatticeNormalForms

set_option linter.style.header false

/-!
# Strong plane groups are geometric wallpaper groups

This module proves the forward geometric bridge.  A framed rank-two lattice is discrete because
bounded sets contain only finitely many of its vectors, and its closed fundamental parallelogram
is a compact orbit-representative set.  The translation subgroup therefore acts properly
discontinuously and cocompactly.  Finiteness of the point group makes the translation subgroup
finite-index, so proper discontinuity passes to the full plane group.

No converse construction is attempted here.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion
open Pointwise

noncomputable section

namespace RankTwoLattice

/-- The topology induced on the carrier of a framed rank-two plane lattice is discrete. -/
theorem carrier_discreteTopology (L : RankTwoLattice Plane) :
    DiscreteTopology L.carrier := by
  rw [L.carrier_eq_zspan_realBasis]
  infer_instance

/-- A bounded set contains only finitely many vectors from a framed rank-two plane lattice. -/
theorem finite_inter_of_isBounded (L : RankTwoLattice Plane)
    {s : Set Plane} (hs : Bornology.IsBounded s) :
    (s ∩ (L.carrier : Set Plane)).Finite := by
  rw [L.carrier_eq_zspan_realBasis]
  exact ZSpan.setFinite_inter L.realBasis hs

/-- The closed fundamental parallelogram associated to the chosen lattice basis. -/
def compactParallelogram (L : RankTwoLattice Plane) : Set Plane :=
  parallelepiped L.realBasis

/-- The closed fundamental parallelogram is compact. -/
theorem isCompact_compactParallelogram (L : RankTwoLattice Plane) :
    IsCompact L.compactParallelogram := by
  simpa [compactParallelogram] using L.realBasis.parallelepiped.isCompact

/--
Every point can be translated into the closed fundamental parallelogram by a lattice vector.
-/
theorem exists_lattice_add_mem_compactParallelogram
    (L : RankTwoLattice Plane) (x : Plane) :
    ∃ t : L.carrier, (t : Plane) + x ∈ L.compactParallelogram := by
  let t : L.carrier :=
    ⟨-(ZSpan.floor L.realBasis x : Plane), by
      rw [L.carrier_eq_zspan_realBasis]
      exact Submodule.neg_mem _ (ZSpan.floor L.realBasis x).property⟩
  refine ⟨t, ?_⟩
  have hfract :
      ZSpan.fract L.realBasis x ∈ ZSpan.fundamentalDomain L.realBasis :=
    ZSpan.fract_mem_fundamentalDomain L.realBasis x
  have hparallelepiped :
      ZSpan.fract L.realBasis x ∈ parallelepiped L.realBasis :=
    ZSpan.fundamentalDomain_subset_parallelepiped L.realBasis hfract
  simpa [t, compactParallelogram, ZSpan.fract_apply, sub_eq_add_neg, add_comm] using
    hparallelepiped

end RankTwoLattice

namespace PlaneGroup

/--
The pure-translation subgroup of a plane group acts properly discontinuously on the plane.
-/
theorem translationSubgroup_isDiscrete (G : PlaneGroup) :
    ProperlyDiscontinuousSMul (translationSubgroup G.carrier) Plane := by
  rw [properlyDiscontinuousSMul_iff]
  intro K M hK hM
  let displacement : translationSubgroup G.carrier → Plane :=
    fun g => translationPart (((g : G.carrier) : EuclideanMotion Plane))
  have hdisplacement_injective : Function.Injective displacement := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    apply AffineIsometryEquiv.ext
    intro x
    rw [← translation_of_mem_translationSubgroup G.carrier g]
    rw [← translation_of_mem_translationSubgroup G.carrier h]
    simp only [translation_apply]
    change translationPart (((g : G.carrier) : EuclideanMotion Plane)) =
      translationPart (((h : G.carrier) : EuclideanMotion Plane)) at hgh
    rw [hgh]
  apply Set.Finite.of_finite_image (f := displacement)
  · apply (G.translationLattice.finite_inter_of_isBounded
      (hM.isBounded.sub hK.isBounded)).subset
    rintro v ⟨g, hg, rfl⟩
    constructor
    · obtain ⟨z, ⟨x, hxK, hgx⟩, hzM⟩ := hg
      refine ⟨z, hzM, x, hxK, ?_⟩
      change z - x =
        translationPart (((g : G.carrier) : EuclideanMotion Plane))
      rw [← hgx]
      change (((g : G.carrier) : EuclideanMotion Plane) x) - x =
        translationPart (((g : G.carrier) : EuclideanMotion Plane))
      rw [← translation_of_mem_translationSubgroup G.carrier g]
      simp
    · rw [G.translationLattice_carrier]
      change displacement g ∈ translationVectors G.carrier
      rw [mem_translationVectors]
      rw [translation_of_mem_translationSubgroup G.carrier g]
      exact (g : G.carrier).property
  · exact hdisplacement_injective.injOn

/-- The translation subgroup has finite index because the point group is finite. -/
theorem translationSubgroup_finiteIndex (G : PlaneGroup) :
    (translationSubgroup G.carrier).FiniteIndex := by
  rw [← pointProjection_ker]
  infer_instance

/--
The full motion subgroup of a plane group acts properly discontinuously on the plane.
-/
theorem motionGroup_isDiscrete (G : PlaneGroup) :
    MotionSubgroup.IsDiscrete G.carrier := by
  let _ : ProperlyDiscontinuousSMul (translationSubgroup G.carrier) Plane :=
    G.translationSubgroup_isDiscrete
  let _ : (translationSubgroup G.carrier).FiniteIndex :=
    G.translationSubgroup_finiteIndex
  let _ : (translationSubgroup G.carrier).IsFiniteRelIndex
      (⊤ : Subgroup G.carrier) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have htop : ProperlyDiscontinuousSMul (⊤ : Subgroup G.carrier) Plane :=
    ProperlyDiscontinuousSMul.ofFiniteRelIndex
      (⊤ : Subgroup G.carrier) (translationSubgroup G.carrier)
  change ProperlyDiscontinuousSMul G.carrier Plane
  rw [properlyDiscontinuousSMul_iff]
  intro K M hK hM
  rw [Subgroup.properlyDiscontinuousSMul_iff] at htop
  simpa using htop hK hM

/--
The translation lattice supplies a compact orbit-representative set for the full motion group.
-/
theorem motionGroup_isCocompact (G : PlaneGroup) :
    MotionSubgroup.IsCocompact G.carrier := by
  rw [MotionSubgroup.isCocompact_iff_exists_compact_orbit_representatives]
  refine ⟨G.translationLattice.compactParallelogram,
    G.translationLattice.isCompact_compactParallelogram, fun x => ?_⟩
  obtain ⟨t, ht⟩ :=
    G.translationLattice.exists_lattice_add_mem_compactParallelogram x
  let γ : G.carrier :=
    ⟨translation (t : Plane),
      (G.mem_translationLattice_iff_translation_mem (t : Plane)).mp t.property⟩
  refine ⟨γ, ?_⟩
  change translation (t : Plane) x ∈ G.translationLattice.compactParallelogram
  simpa [translation_apply] using ht

/-- The orbit space of every strong plane group is compact. -/
theorem motionGroup_compactOrbitSpace (G : PlaneGroup) :
    CompactSpace (MotionSubgroup.OrbitSpace G.carrier) :=
  G.motionGroup_isCocompact.compact_orbitSpace

/--
Package a strong plane group as a geometric wallpaper group without changing its motion carrier.
-/
def toGeometricWallpaperGroup (G : PlaneGroup) : GeometricWallpaperGroup where
  carrier := G.carrier
  isDiscrete := G.motionGroup_isDiscrete
  isCocompact := G.motionGroup_isCocompact

/-- The strong-to-geometric conversion leaves the motion subgroup unchanged. -/
@[simp]
theorem toGeometricWallpaperGroup_carrier (G : PlaneGroup) :
    G.toGeometricWallpaperGroup.carrier = G.carrier :=
  rfl

end PlaneGroup

end

end WallpaperGroups
