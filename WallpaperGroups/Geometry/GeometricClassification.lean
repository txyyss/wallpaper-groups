import WallpaperGroups.Classification.PlaneGroupClasses
import WallpaperGroups.Geometry.MotionType
import WallpaperGroups.Geometry.StrongToGeometric
import WallpaperGroups.Geometry.TranslationLatticeRecovery

set_option linter.style.header false

/-!
# Geometric wallpaper groups as strong plane groups

This module completes the converse geometric bridge.  Every discrete cocompact subgroup of plane
Euclidean motions is packaged as a strong `PlaneGroup` on exactly the same motion carrier, using
the full translation lattice recovered in M8c-b and the finite point group recovered in M8c-a.

The chosen lattice basis is not canonical.  Same-carrier strong structures are therefore compared
only through `PlaneGroup.Equivalent`.  On geometric wallpaper groups themselves, the public
equivalence is the direct textbook relation preserving translations, rotations, reflections, and
glide reflections.  Adapters to M8a make the geometric seventeen-class theorem a corollary of the
existing Version 1 classification.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-! ## The recovered strong plane group -/

namespace GeometricWallpaperGroup

/--
Package a geometric wallpaper group as a strong plane group without changing its motion carrier.

The translation lattice is the complete lattice recovered in M8c-b; point-group finiteness is the
M8c-a instance.
-/
def toPlaneGroup (X : GeometricWallpaperGroup) : PlaneGroup where
  carrier := X.carrier
  translationLattice := X.translationLattice
  translationLattice_carrier := X.translationLattice_carrier
  pointGroup_finite := X.pointGroupFinite

/-- The geometric-to-strong conversion leaves the motion subgroup unchanged. -/
@[simp]
theorem toPlaneGroup_carrier (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.carrier = X.carrier :=
  rfl

/-- The recovered strong translation lattice has exactly the original translation module. -/
@[simp]
theorem toPlaneGroup_translationLattice_carrier
    (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.translationLattice.carrier =
      (translationVectors X.carrier).toIntSubmodule :=
  X.translationLattice_carrier

end GeometricWallpaperGroup

namespace PlaneGroup

/--
Strong plane-group structures on the same motion subgroup are equivalent.

The identity-on-ambient-elements subgroup equivalence preserves the full translation kernel.
Consequently no stored lattice basis or proof-field choice is visible to `PlaneGroup.Equivalent`.
-/
theorem equivalent_of_carrier_eq
    {G H : PlaneGroup} (h : G.carrier = H.carrier) :
    G.Equivalent H := by
  refine ⟨{
    toMulEquiv := MulEquiv.subgroupCongr h
    map_translationSubgroup := ?_
  }⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change linearPart (x : EuclideanMotion Plane) = 1 at hx
    change linearPart
      (((MulEquiv.subgroupCongr h x : H.carrier) :
        EuclideanMotion Plane)) = 1
    simpa using hx
  · intro hy
    change linearPart (y : EuclideanMotion Plane) = 1 at hy
    let e : G.carrier ≃* H.carrier :=
      MulEquiv.subgroupCongr h
    let x : G.carrier := e.symm y
    refine ⟨x, ?_, e.apply_symm_apply y⟩
    change linearPart (x : EuclideanMotion Plane) = 1
    simpa [e, x] using hy

/--
The strong-to-geometric-to-strong round trip preserves the strong equivalence class.

Structural equality is intentionally not claimed because the recovered integer basis may differ
from the original stored basis.
-/
theorem toGeometric_toPlaneGroup (G : PlaneGroup) :
    G.Equivalent G.toGeometricWallpaperGroup.toPlaneGroup :=
  equivalent_of_carrier_eq rfl

end PlaneGroup

namespace GeometricWallpaperGroup

/--
Any valid strong package on the original geometric motion carrier is equivalent to the recovered
one, independently of its chosen lattice basis or proof fields.
-/
theorem toPlaneGroup_choice_independent
    (X : GeometricWallpaperGroup) (G : PlaneGroup)
    (hcarrier : G.carrier = X.carrier) :
    G.Equivalent X.toPlaneGroup :=
  PlaneGroup.equivalent_of_carrier_eq
    (hcarrier.trans X.toPlaneGroup_carrier.symm)

end GeometricWallpaperGroup

/-! ## Direct textbook equivalence of geometric groups -/

namespace GeometricWallpaperGroup

/--
An abstract isomorphism of geometric wallpaper groups preserving all four textbook motion types.

This structure is stated directly on the two geometric motion carriers.  It contains no compact
cover, recovered lattice, chosen basis, ambient conjugacy, or metric-preservation datum.
-/
structure MotionTypePreservingIso
    (X Y : GeometricWallpaperGroup) where
  toMulEquiv : X.carrier ≃* Y.carrier
  map_isTranslation_iff : ∀ g : X.carrier,
    PlaneMotion.IsTranslation (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsTranslation
        ((toMulEquiv g : Y.carrier) : EuclideanMotion Plane)
  map_isRotation_iff : ∀ g : X.carrier,
    PlaneMotion.IsRotation (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsRotation
        ((toMulEquiv g : Y.carrier) : EuclideanMotion Plane)
  map_isReflection_iff : ∀ g : X.carrier,
    PlaneMotion.IsReflection (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsReflection
        ((toMulEquiv g : Y.carrier) : EuclideanMotion Plane)
  map_isGlideReflection_iff : ∀ g : X.carrier,
    PlaneMotion.IsGlideReflection (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsGlideReflection
        ((toMulEquiv g : Y.carrier) : EuclideanMotion Plane)

namespace MotionTypePreservingIso

variable {X Y Z : GeometricWallpaperGroup}

/-- Identity direct motion-type-preserving isomorphism. -/
def refl (X : GeometricWallpaperGroup) :
    MotionTypePreservingIso X X where
  toMulEquiv := MulEquiv.refl X.carrier
  map_isTranslation_iff _ := Iff.rfl
  map_isRotation_iff _ := Iff.rfl
  map_isReflection_iff _ := Iff.rfl
  map_isGlideReflection_iff _ := Iff.rfl

/-- Inverse of a direct motion-type-preserving isomorphism. -/
def symm (e : MotionTypePreservingIso X Y) :
    MotionTypePreservingIso Y X where
  toMulEquiv := e.toMulEquiv.symm
  map_isTranslation_iff g := by
    simpa using (e.map_isTranslation_iff (e.toMulEquiv.symm g)).symm
  map_isRotation_iff g := by
    simpa using (e.map_isRotation_iff (e.toMulEquiv.symm g)).symm
  map_isReflection_iff g := by
    simpa using (e.map_isReflection_iff (e.toMulEquiv.symm g)).symm
  map_isGlideReflection_iff g := by
    simpa using (e.map_isGlideReflection_iff (e.toMulEquiv.symm g)).symm

/-- Composition of direct motion-type-preserving isomorphisms. -/
def trans (e : MotionTypePreservingIso X Y)
    (f : MotionTypePreservingIso Y Z) :
    MotionTypePreservingIso X Z where
  toMulEquiv := e.toMulEquiv.trans f.toMulEquiv
  map_isTranslation_iff g :=
    (e.map_isTranslation_iff g).trans
      (f.map_isTranslation_iff (e.toMulEquiv g))
  map_isRotation_iff g :=
    (e.map_isRotation_iff g).trans
      (f.map_isRotation_iff (e.toMulEquiv g))
  map_isReflection_iff g :=
    (e.map_isReflection_iff g).trans
      (f.map_isReflection_iff (e.toMulEquiv g))
  map_isGlideReflection_iff g :=
    (e.map_isGlideReflection_iff g).trans
      (f.map_isGlideReflection_iff (e.toMulEquiv g))

/-- Regard a direct geometric isomorphism as an M8a isomorphism of recovered strong groups. -/
def toPlaneGroup (e : MotionTypePreservingIso X Y) :
    WallpaperGroups.MotionTypePreservingIso
      X.toPlaneGroup Y.toPlaneGroup where
  toMulEquiv := e.toMulEquiv
  map_isTranslation_iff := e.map_isTranslation_iff
  map_isRotation_iff := e.map_isRotation_iff
  map_isReflection_iff := e.map_isReflection_iff
  map_isGlideReflection_iff := e.map_isGlideReflection_iff

/-- Forget recovered strong structure from an M8a motion-type-preserving isomorphism. -/
def ofPlaneGroup
    (e : WallpaperGroups.MotionTypePreservingIso
      X.toPlaneGroup Y.toPlaneGroup) :
    MotionTypePreservingIso X Y where
  toMulEquiv := e.toMulEquiv
  map_isTranslation_iff := e.map_isTranslation_iff
  map_isRotation_iff := e.map_isRotation_iff
  map_isReflection_iff := e.map_isReflection_iff
  map_isGlideReflection_iff := e.map_isGlideReflection_iff

/--
Turn an M8a isomorphism from a recovered strong group to an existing strong target into a direct
geometric isomorphism to the target's M8b image.
-/
def ofPlaneGroupTarget {X : GeometricWallpaperGroup} {G : PlaneGroup}
    (e : WallpaperGroups.MotionTypePreservingIso X.toPlaneGroup G) :
    MotionTypePreservingIso X G.toGeometricWallpaperGroup where
  toMulEquiv := e.toMulEquiv
  map_isTranslation_iff := e.map_isTranslation_iff
  map_isRotation_iff := e.map_isRotation_iff
  map_isReflection_iff := e.map_isReflection_iff
  map_isGlideReflection_iff := e.map_isGlideReflection_iff

/--
Regard a direct geometric isomorphism to an M8b image as an M8a isomorphism to the original
strong target.
-/
def toPlaneGroupTarget {X : GeometricWallpaperGroup} {G : PlaneGroup}
    (e : MotionTypePreservingIso X G.toGeometricWallpaperGroup) :
    WallpaperGroups.MotionTypePreservingIso X.toPlaneGroup G where
  toMulEquiv := e.toMulEquiv
  map_isTranslation_iff := e.map_isTranslation_iff
  map_isRotation_iff := e.map_isRotation_iff
  map_isReflection_iff := e.map_isReflection_iff
  map_isGlideReflection_iff := e.map_isGlideReflection_iff

end MotionTypePreservingIso

/-- Direct textbook equivalence is nonempty direct motion-type-preserving isomorphism. -/
def TextbookEquivalent (X Y : GeometricWallpaperGroup) : Prop :=
  Nonempty (MotionTypePreservingIso X Y)

namespace TextbookEquivalent

/-- Every geometric wallpaper group is directly textbook-equivalent to itself. -/
theorem refl (X : GeometricWallpaperGroup) :
    TextbookEquivalent X X :=
  ⟨MotionTypePreservingIso.refl X⟩

/-- Direct geometric textbook equivalence is symmetric. -/
theorem symm {X Y : GeometricWallpaperGroup}
    (h : TextbookEquivalent X Y) :
    TextbookEquivalent Y X := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/-- Direct geometric textbook equivalence is transitive. -/
theorem trans {X Y Z : GeometricWallpaperGroup}
    (hXY : TextbookEquivalent X Y)
    (hYZ : TextbookEquivalent Y Z) :
    TextbookEquivalent X Z := by
  rcases hXY with ⟨e⟩
  rcases hYZ with ⟨f⟩
  exact ⟨e.trans f⟩

end TextbookEquivalent

/-- Direct geometric textbook equivalence is an equivalence relation. -/
theorem textbookEquivalent_equivalence :
    Equivalence TextbookEquivalent := by
  constructor
  · exact TextbookEquivalent.refl
  · intro X Y
    exact TextbookEquivalent.symm
  · intro X Y Z
    exact TextbookEquivalent.trans

/-- Geometric wallpaper groups carry the direct textbook-equivalence setoid. -/
instance textbookEquivalentSetoid : Setoid GeometricWallpaperGroup where
  r := TextbookEquivalent
  iseqv := textbookEquivalent_equivalence

/-- Direct geometric equivalence is exactly M8a equivalence of the recovered strong groups. -/
theorem textbookEquivalent_iff_toPlaneGroup
    (X Y : GeometricWallpaperGroup) :
    TextbookEquivalent X Y ↔
      PlaneGroup.TextbookEquivalent X.toPlaneGroup Y.toPlaneGroup := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toPlaneGroup⟩
  · rintro ⟨e⟩
    exact ⟨MotionTypePreservingIso.ofPlaneGroup e⟩

/--
Direct geometric textbook equivalence is also exactly Version 1 translation-preserving
equivalence of the recovered strong groups.
-/
theorem textbookEquivalent_iff_equivalent
    (X Y : GeometricWallpaperGroup) :
    TextbookEquivalent X Y ↔
      PlaneGroup.Equivalent X.toPlaneGroup Y.toPlaneGroup := by
  rw [textbookEquivalent_iff_toPlaneGroup,
    PlaneGroup.textbookEquivalent_iff_equivalent]

/--
The geometric-to-strong-to-geometric round trip preserves direct textbook equivalence.
-/
theorem toPlaneGroup_toGeometric (X : GeometricWallpaperGroup) :
    TextbookEquivalent
      X X.toPlaneGroup.toGeometricWallpaperGroup :=
  ⟨MotionTypePreservingIso.refl X⟩

/-- The geometric-to-strong-to-geometric round trip leaves the motion carrier unchanged. -/
@[simp]
theorem toPlaneGroup_toGeometric_carrier
    (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.toGeometricWallpaperGroup.carrier = X.carrier :=
  rfl

/-- Geometric wallpaper groups modulo direct textbook equivalence. -/
abbrev EquivalenceClass :=
  Quotient GeometricWallpaperGroup.textbookEquivalentSetoid

end GeometricWallpaperGroup

/-! ## Standard geometric models and the seventeen-class theorem -/

namespace WallpaperType

/-- The standard geometric model obtained by applying the canonical M8b conversion. -/
def geometricModel (w : WallpaperType) : GeometricWallpaperGroup :=
  w.model.toGeometricWallpaperGroup

/-- A standard geometric model has the same motion carrier as its strong model. -/
@[simp]
theorem geometricModel_carrier (w : WallpaperType) :
    w.geometricModel.carrier = w.model.carrier :=
  rfl

end WallpaperType

/--
Every geometric wallpaper group is directly textbook-equivalent to exactly one of the seventeen
standard geometric models.

The proof only wraps M8a's `textbook_classification` with carrier-level conversion adapters; it
does not repeat any Version 1 classification case.
-/
theorem geometric_classification (X : GeometricWallpaperGroup) :
    ∃! w : WallpaperType,
      GeometricWallpaperGroup.TextbookEquivalent
        X w.geometricModel := by
  obtain ⟨w, hw, hunique⟩ :=
    textbook_classification X.toPlaneGroup
  refine ⟨w, ?_, ?_⟩
  · rcases hw with ⟨e⟩
    exact
      ⟨GeometricWallpaperGroup.MotionTypePreservingIso.ofPlaneGroupTarget e⟩
  · intro v hv
    apply hunique v
    rcases hv with ⟨e⟩
    exact
      ⟨GeometricWallpaperGroup.MotionTypePreservingIso.toPlaneGroupTarget e⟩

namespace WallpaperType

/-- Two standard geometric models are directly equivalent exactly when their labels agree. -/
theorem geometricModels_textbookEquivalent_iff
    (w v : WallpaperType) :
    GeometricWallpaperGroup.TextbookEquivalent
      w.geometricModel v.geometricModel ↔ w = v := by
  constructor
  · intro h
    exact (geometric_classification w.geometricModel).unique
      (GeometricWallpaperGroup.TextbookEquivalent.refl w.geometricModel)
      h
  · rintro rfl
    exact
      GeometricWallpaperGroup.TextbookEquivalent.refl
        w.geometricModel

/-- Map a wallpaper label to the direct geometric equivalence class of its standard model. -/
def toGeometricEquivalenceClass
    (w : WallpaperType) :
    GeometricWallpaperGroup.EquivalenceClass :=
  Quotient.mk'' w.geometricModel

/-- Distinct wallpaper labels give distinct direct geometric equivalence classes. -/
theorem toGeometricEquivalenceClass_injective :
    Function.Injective toGeometricEquivalenceClass := by
  intro w v h
  apply (geometricModels_textbookEquivalent_iff w v).mp
  exact Quotient.exact h

/-- Every direct geometric equivalence class has a standard wallpaper representative. -/
theorem toGeometricEquivalenceClass_surjective :
    Function.Surjective toGeometricEquivalenceClass := by
  intro q
  induction q using Quotient.inductionOn with
  | _ X =>
      obtain ⟨w, hw, _⟩ := geometric_classification X
      refine ⟨w, Quotient.sound ?_⟩
      exact GeometricWallpaperGroup.TextbookEquivalent.symm hw

/-- Wallpaper labels are equivalent to direct geometric wallpaper-group equivalence classes. -/
def geometricEquivalenceClassEquiv :
    WallpaperType ≃ GeometricWallpaperGroup.EquivalenceClass :=
  Equiv.ofBijective toGeometricEquivalenceClass
    ⟨toGeometricEquivalenceClass_injective,
      toGeometricEquivalenceClass_surjective⟩

/-- The geometric quotient equivalence sends a label to its standard geometric model class. -/
@[simp]
theorem geometricEquivalenceClassEquiv_apply
    (w : WallpaperType) :
    geometricEquivalenceClassEquiv w =
      toGeometricEquivalenceClass w :=
  rfl

end WallpaperType

namespace GeometricWallpaperGroup

/-- The direct geometric equivalence quotient is finite. -/
noncomputable instance equivalenceClassFinite :
    Finite GeometricWallpaperGroup.EquivalenceClass :=
  Finite.of_equiv WallpaperType
    WallpaperType.geometricEquivalenceClassEquiv

/--
There are exactly seventeen direct textbook-equivalence classes of geometric wallpaper groups.
-/
@[simp]
theorem equivalenceClass_card_eq_seventeen :
    Nat.card GeometricWallpaperGroup.EquivalenceClass = 17 := by
  calc
    Nat.card GeometricWallpaperGroup.EquivalenceClass =
        Nat.card WallpaperType :=
      Nat.card_congr WallpaperType.geometricEquivalenceClassEquiv.symm
    _ = 17 := WallpaperType.card_eq_seventeen

end GeometricWallpaperGroup

end

end WallpaperGroups
