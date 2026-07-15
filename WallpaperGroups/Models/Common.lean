import WallpaperGroups.Basic.PlaneGroup

set_option linter.style.header false

/-!
# Transparent symmorphic plane-group models

This file provides the common normal form used by the symmorphic standard models.  A motion is
in the carrier exactly when its translation part belongs to a selected rank-two lattice and its
linear part belongs to a selected finite point group.  The two defining conditions make the full
translation subgroup and point group computable without appealing to subgroup generators.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-- A linear point group preserves a lattice when each point element sends lattice vectors back
to lattice vectors. -/
def LatticePreservingPointGroup
    (L : RankTwoLattice Plane)
    (K : Subgroup (Plane ≃ₗᵢ[ℝ] Plane)) : Prop :=
  ∀ A : K, ∀ t : Plane, t ∈ L.carrier →
    (A : Plane ≃ₗᵢ[ℝ] Plane) t ∈ L.carrier

/-- The transparent symmorphic carrier associated to a lattice and a lattice-preserving point
group.  Its elements are precisely the affine motions with translation part in `L` and linear
part in `K`. -/
def symmorphicCarrier
    (L : RankTwoLattice Plane)
    (K : Subgroup (Plane ≃ₗᵢ[ℝ] Plane))
    (hK : LatticePreservingPointGroup L K) :
    Subgroup (EuclideanMotion Plane) where
  carrier := {g | translationPart g ∈ L.carrier ∧ linearPart g ∈ K}
  one_mem' := by
    constructor
    · exact L.carrier.zero_mem
    · rw [linearPart_one]
      exact K.one_mem
  mul_mem' := by
    intro g h hg hh
    constructor
    · rw [translationPart_mul]
      exact L.carrier.add_mem hg.1
        (hK ⟨linearPart g, hg.2⟩ (translationPart h) hh.1)
    · rw [linearPart_mul]
      exact K.mul_mem hg.2 hh.2
  inv_mem' := by
    intro g hg
    constructor
    · rw [translationPart_inv]
      exact L.carrier.neg_mem
        (hK ⟨(linearPart g)⁻¹, K.inv_mem hg.2⟩ (translationPart g) hg.1)
    · rw [linearPart_inv]
      exact K.inv_mem hg.2

/-- Membership in a symmorphic carrier is the advertised translation/linear-part normal form. -/
@[simp]
theorem mem_symmorphicCarrier
    (L : RankTwoLattice Plane)
    (K : Subgroup (Plane ≃ₗᵢ[ℝ] Plane))
    (hK : LatticePreservingPointGroup L K)
    (g : EuclideanMotion Plane) :
    g ∈ symmorphicCarrier L K hK ↔
      translationPart g ∈ L.carrier ∧ linearPart g ∈ K :=
  Iff.rfl

/-- The pure translations of the symmorphic carrier are exactly the selected lattice. -/
theorem symmorphicCarrier_translationVectors
    (L : RankTwoLattice Plane)
    (K : Subgroup (Plane ≃ₗᵢ[ℝ] Plane))
    (hK : LatticePreservingPointGroup L K) :
    translationVectors (symmorphicCarrier L K hK) = L.toAddSubgroup := by
  ext t
  change
    (translationPart (translation t) ∈ L.carrier ∧
      linearPart (translation t) ∈ K) ↔ t ∈ L.toAddSubgroup
  rw [translationPart_translation, linearPart_translation]
  exact and_iff_left K.one_mem

/-- The point group of the symmorphic carrier is exactly the selected linear subgroup. -/
theorem symmorphicCarrier_pointGroup
    (L : RankTwoLattice Plane)
    (K : Subgroup (Plane ≃ₗᵢ[ℝ] Plane))
    (hK : LatticePreservingPointGroup L K) :
    pointGroup (symmorphicCarrier L K hK) = K := by
  ext A
  constructor
  · rw [mem_pointGroup_iff]
    rintro ⟨g, hg⟩
    rw [← hg]
    exact g.property.2
  · intro hA
    rw [mem_pointGroup_iff]
    refine ⟨⟨pureLinear A, ?_⟩, ?_⟩
    · rw [mem_symmorphicCarrier, translationPart_pureLinear, linearPart_pureLinear]
      exact ⟨L.carrier.zero_mem, hA⟩
    · exact linearPart_pureLinear A

/-- A finite lattice-preserving linear point group and a rank-two lattice determine a
symmorphic `PlaneGroup` with transparent normal forms. -/
def symmorphicPlaneGroup
    (L : RankTwoLattice Plane)
    (K : Subgroup (Plane ≃ₗᵢ[ℝ] Plane))
    (hK : LatticePreservingPointGroup L K)
    [Finite K] : PlaneGroup where
  carrier := symmorphicCarrier L K hK
  translationLattice := L
  translationLattice_carrier := by
    rw [symmorphicCarrier_translationVectors]
    rfl
  pointGroup_finite := by
    rw [symmorphicCarrier_pointGroup]
    infer_instance

end

end WallpaperGroups
