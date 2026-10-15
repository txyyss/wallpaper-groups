module

import WallpaperGroups

/-!
# Root public-API regression test

This module deliberately imports only `WallpaperGroups`.  It checks representative
visibility and only those definitional reductions that are intentional API contracts.
-/

set_option autoImplicit false

namespace WallpaperGroups.Prototype.PublicAPI

open EuclideanMotion

noncomputable section

/-! ## Representative root visibility -/

#check Plane
#check EuclideanMotion
#check RankTwoLattice
#check PlaneGroup
#check TranslationPreservingIso
#check PlaneGroup.Equivalent
#check CrystallographicOrder
#check WallpaperType
#check GeometricWallpaperGroup

#check AdditiveAction
#check NormalizedCocycle
#check NormalizedCochain
#check CocycleCohomologous
#check TwistedProduct
#check NormalizedSection
#check ExtensionOverAction
#check ExtensionOverAction.EquivAlong
#check AdditiveAction.Equiv
#check @NormalizedCocycle.transport
#check @GroupExtension.transportEndpoints
#check @ExtensionOverAction.transport
#check @NormalizedSection.twistedProductExtensionEquiv

#check @classification
#check @textbook_classification
#check @geometric_classification
#check @ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous
#check @ExtensionOverAction.equivAlong_iff_cocycleCohomologous
#check PlaneGroup.equivalenceClass_card_eq_seventeen
#check GeometricWallpaperGroup.equivalenceClass_card_eq_seventeen

/-! ## Stable foundational reductions -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example (g : EuclideanMotion E) :
    translationPart g = g 0 :=
  rfl

example (t x : E) :
    translation t x = t + x :=
  rfl

example (G H : PlaneGroup) :
    PlaneGroup.Equivalent G H ↔
      Nonempty (TranslationPreservingIso G H) :=
  Iff.rfl

example :
    CrystallographicOrder.toNat .six = 6 :=
  rfl

example :
    WallpaperType.pointGroupOrder .p4g = 8 :=
  rfl

example :
    WallpaperType.model .p1 = p1Model :=
  rfl

/-! ## Approved geometric definitions -/

example (g : EuclideanMotion Plane) :
    PlaneMotion.IsTranslation g ↔ linearPart g = 1 :=
  Iff.rfl

example (g : EuclideanMotion Plane) :
    PlaneMotion.IsRotation g ↔
      0 < PlaneMotion.determinant g ∧
        ¬ PlaneMotion.IsTranslation g :=
  Iff.rfl

example (g : EuclideanMotion Plane) :
    PlaneMotion.IsReflection g ↔
      PlaneMotion.determinant g < 0 ∧ PlaneMotion.HasFixedPoint g :=
  Iff.rfl

example (g : EuclideanMotion Plane) :
    PlaneMotion.IsGlideReflection g ↔
      PlaneMotion.determinant g < 0 ∧ ¬ PlaneMotion.HasFixedPoint g :=
  Iff.rfl

example (Γ : Subgroup (EuclideanMotion Plane)) :
    MotionSubgroup.IsDiscrete Γ ↔
      ProperlyDiscontinuousSMul Γ Plane :=
  Iff.rfl

example (Γ : Subgroup (EuclideanMotion Plane)) :
    MotionSubgroup.IsCocompact Γ ↔
      ∃ K : Set Plane, IsCompact K ∧
        ⋃ γ : Γ, (γ • ·) '' K = Set.univ :=
  Iff.rfl

example (G H : PlaneGroup) :
    PlaneGroup.TextbookEquivalent G H ↔
      Nonempty (MotionTypePreservingIso G H) :=
  Iff.rfl

example (X Y : GeometricWallpaperGroup) :
    GeometricWallpaperGroup.TextbookEquivalent X Y ↔
      Nonempty
        (GeometricWallpaperGroup.MotionTypePreservingIso X Y) :=
  Iff.rfl

example (G H : PlaneGroup) :
    G.TextbookEquivalent H ↔ G.Equivalent H :=
  PlaneGroup.textbookEquivalent_iff_equivalent G H

example (X Y : GeometricWallpaperGroup) :
    X.TextbookEquivalent Y ↔
      X.toPlaneGroup.Equivalent Y.toPlaneGroup :=
  GeometricWallpaperGroup.textbookEquivalent_iff_equivalent X Y

/-! ## Explicit extension formulas -/

section ExtensionCore

variable {H T : Type*} [Group H] [AddCommGroup T]
variable {ρ : AdditiveAction H T}

example (h : H) (t : T) :
    ρ.apply h t = (ρ h).toAdd t :=
  rfl

example (b : NormalizedCochain H T) (g h : H) :
    b.coboundary ρ g h =
      b g + ρ.apply g (b h) - b (g * h) :=
  rfl

example (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) (g h : H) :
    c.changeBy b g h =
      c g h + b.coboundary ρ g h :=
  rfl

example (c : NormalizedCocycle ρ)
    (x y : TwistedProduct c) :
    (x * y).left =
      x.left + ρ.apply x.right y.left + c x.right y.right :=
  TwistedProduct.mul_left x y

end ExtensionCore

/-! ## Opaque constructions through stable observation theorems -/

example (G : PlaneGroup) :
    G.toGeometricWallpaperGroup.carrier = G.carrier :=
  PlaneGroup.toGeometricWallpaperGroup_carrier G

example (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.carrier = X.carrier :=
  GeometricWallpaperGroup.toPlaneGroup_carrier X

example (G : PlaneGroup) :
    G.Equivalent G.toGeometricWallpaperGroup.toPlaneGroup :=
  PlaneGroup.toGeometric_toPlaneGroup G

example (X : GeometricWallpaperGroup) :
    X.TextbookEquivalent X.toPlaneGroup.toGeometricWallpaperGroup :=
  GeometricWallpaperGroup.toPlaneGroup_toGeometric X

example (w : WallpaperType) :
    w.model.translationLattice = w.lattice :=
  WallpaperType.model_translationLattice w

example (G : PlaneGroup) :
    ∃! w : WallpaperType,
      PlaneGroup.Equivalent G (WallpaperType.model w) :=
  classification G

example (X : GeometricWallpaperGroup) :
    ∃! w : WallpaperType,
      GeometricWallpaperGroup.TextbookEquivalent X w.geometricModel :=
  geometric_classification X

end

end WallpaperGroups.Prototype.PublicAPI
