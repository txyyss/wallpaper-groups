import WallpaperGroups.Classification.Wallpaper

set_option linter.style.header false

/-!
# Plane-motion types and textbook equivalence

This module defines the four standard types of Euclidean motions of the plane.  The identity is
treated as the zero translation, and rotations exclude every translation.  Reflections and glide
reflections are distinguished geometrically by the presence of a fixed point.  For
orientation-reversing motions, having a fixed point is proved equivalent to squaring to the
identity.  That algebraic characterization lets a translation-preserving abstract isomorphism
preserve reflections and glide reflections without being induced by an ambient Euclidean
conjugacy.

The resulting textbook-style equivalence is proved logically equivalent to the
translation-preserving equivalence used by the Version 1 classification.  The final seventeen-class
statement is therefore a corollary of the existing classifier.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-! ## The four types of plane motions -/

namespace PlaneMotion

/-- The real determinant of the linear part of a Euclidean motion of the plane. -/
def determinant (g : EuclideanMotion Plane) : ℝ :=
  LinearMap.det
    ((linearPart g).toLinearEquiv : Plane →ₗ[ℝ] Plane)

/-- A plane motion has a fixed point when it fixes at least one point of the affine plane. -/
def HasFixedPoint (g : EuclideanMotion Plane) : Prop :=
  ∃ x : Plane, g x = x

/--
A translation is a plane motion with identity linear part.  This convention includes the identity
motion as translation by zero.
-/
def IsTranslation (g : EuclideanMotion Plane) : Prop :=
  linearPart g = 1

/--
A rotation is an orientation-preserving plane motion that is not a translation.  In particular,
the identity is not classified as a rotation.
-/
def IsRotation (g : EuclideanMotion Plane) : Prop :=
  0 < determinant g ∧ ¬ IsTranslation g

/-- A reflection is an orientation-reversing plane motion with a fixed point. -/
def IsReflection (g : EuclideanMotion Plane) : Prop :=
  determinant g < 0 ∧ HasFixedPoint g

/-- A glide reflection is an orientation-reversing plane motion without a fixed point. -/
def IsGlideReflection (g : EuclideanMotion Plane) : Prop :=
  determinant g < 0 ∧ ¬ HasFixedPoint g

/-- The determinant of the linear part of a Euclidean motion is nonzero. -/
theorem determinant_ne_zero (g : EuclideanMotion Plane) :
    determinant g ≠ 0 := by
  rw [determinant, ← LinearEquiv.coe_det]
  exact Units.ne_zero _

/-- A negative-determinant plane motion has an involutive linear part. -/
theorem negative_linearPart_sq {g : EuclideanMotion Plane}
    (hneg : determinant g < 0) :
    linearPart g ^ 2 = 1 :=
  negative_isometry_sq (linearPart g) hneg

/-- The linear-part definition of translation agrees with being the corresponding pure motion. -/
theorem isTranslation_iff_eq_translation (g : EuclideanMotion Plane) :
    IsTranslation g ↔ g = translation (translationPart g) :=
  ⟨eq_translation_of_linearPart_eq_one,
    fun h => by
      unfold IsTranslation
      rw [h, linearPart_translation]⟩

/-- Every rotation in the determinant/nontranslation sense has a fixed point. -/
theorem isRotation_hasFixedPoint {g : EuclideanMotion Plane}
    (hrot : IsRotation g) :
    HasFixedPoint g := by
  let f : Plane →ₗ[ℝ] Plane :=
    LinearMap.id - (linearPart g).toLinearEquiv.toLinearMap
  have hinjective : Function.Injective f := by
    intro x y hxy
    have hsub : f (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hfixed : linearPart g (x - y) = x - y := by
      change (x - y) - linearPart g (x - y) = 0 at hsub
      exact (sub_eq_zero.mp hsub).symm
    by_contra hne
    have hsub_ne : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hone : 0 < LinearMap.det
        (((1 : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv :
          Plane →ₗ[ℝ] Plane)) := by
      change 0 < LinearMap.det (LinearMap.id : Plane →ₗ[ℝ] Plane)
      rw [LinearMap.det_id]
      norm_num
    have hlinear : linearPart g = 1 := by
      apply positive_isometry_eq_of_apply_eq hrot.1 hone hsub_ne
      simpa using hfixed
    exact hrot.2 hlinear
  have hsurjective : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinjective
  obtain ⟨x, hx⟩ := hsurjective (translationPart g)
  refine ⟨x, ?_⟩
  rw [apply_eq_translationPart_add]
  change x - linearPart g x = translationPart g at hx
  rw [← hx]
  module

/-- Every involutive plane motion fixes the midpoint of the origin and its image. -/
theorem hasFixedPoint_of_sq_eq_one {g : EuclideanMotion Plane}
    (hsq : g ^ 2 = 1) :
    HasFixedPoint g := by
  let v : Plane := translationPart g
  refine ⟨(2 : ℝ)⁻¹ • v, ?_⟩
  rw [apply_eq_translationPart_add]
  change v + linearPart g ((2 : ℝ)⁻¹ • v) = (2 : ℝ)⁻¹ • v
  rw [map_smul]
  have hv : v + linearPart g v = 0 := by
    have h := congrArg translationPart hsq
    simpa only [pow_two, translationPart_mul, translationPart_one] using h
  have hAv : linearPart g v = -v := eq_neg_of_add_eq_zero_right hv
  rw [hAv]
  module

/--
A negative-determinant motion with a fixed point is an involution: its linear part is involutive,
and the resulting square is a translation fixing that point.
-/
theorem sq_eq_one_of_negative_hasFixedPoint {g : EuclideanMotion Plane}
    (hneg : determinant g < 0) (hfix : HasFixedPoint g) :
    g ^ 2 = 1 := by
  obtain ⟨x, hx⟩ := hfix
  have hlinear : linearPart (g ^ 2) = 1 := by
    rw [map_pow, negative_linearPart_sq hneg]
  have htranslation :
      g ^ 2 = translation (translationPart (g ^ 2)) :=
    eq_translation_of_linearPart_eq_one hlinear
  have hfixsq : (g ^ 2) x = x := by
    simp [pow_two, hx]
  rw [htranslation, translation_apply] at hfixsq
  have hzero : translationPart (g ^ 2) = 0 :=
    add_eq_right.mp hfixsq
  rw [htranslation, hzero, translation_zero]

/-- For a reversing motion, having a fixed point is equivalent to squaring to the identity. -/
theorem negative_hasFixedPoint_iff_sq_eq_one {g : EuclideanMotion Plane}
    (hneg : determinant g < 0) :
    HasFixedPoint g ↔ g ^ 2 = 1 :=
  ⟨sq_eq_one_of_negative_hasFixedPoint hneg, hasFixedPoint_of_sq_eq_one⟩

/-- Algebraic characterization of reflections by determinant sign and square. -/
theorem isReflection_iff {g : EuclideanMotion Plane} :
    IsReflection g ↔ determinant g < 0 ∧ g ^ 2 = 1 := by
  constructor
  · rintro ⟨hneg, hfix⟩
    exact ⟨hneg, (negative_hasFixedPoint_iff_sq_eq_one hneg).mp hfix⟩
  · rintro ⟨hneg, hsq⟩
    exact ⟨hneg, (negative_hasFixedPoint_iff_sq_eq_one hneg).mpr hsq⟩

/-- Algebraic characterization of glide reflections by determinant sign and nontrivial square. -/
theorem isGlideReflection_iff {g : EuclideanMotion Plane} :
    IsGlideReflection g ↔ determinant g < 0 ∧ g ^ 2 ≠ 1 := by
  constructor
  · rintro ⟨hneg, hnfix⟩
    exact ⟨hneg, fun hsq => hnfix
      ((negative_hasFixedPoint_iff_sq_eq_one hneg).mpr hsq)⟩
  · rintro ⟨hneg, hnsq⟩
    exact ⟨hneg, fun hfix => hnsq
      ((negative_hasFixedPoint_iff_sq_eq_one hneg).mp hfix)⟩

/-- Every Euclidean motion of the plane belongs to one of the four standard motion types. -/
theorem decomposition (g : EuclideanMotion Plane) :
    IsTranslation g ∨ IsRotation g ∨ IsReflection g ∨
      IsGlideReflection g := by
  rcases lt_or_gt_of_ne (determinant_ne_zero g) with hneg | hpos
  · by_cases hfix : HasFixedPoint g
    · exact Or.inr (Or.inr (Or.inl ⟨hneg, hfix⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hneg, hfix⟩))
  · by_cases htrans : IsTranslation g
    · exact Or.inl htrans
    · exact Or.inr (Or.inl ⟨hpos, htrans⟩)

/-- A translation cannot be a rotation. -/
theorem isTranslation_not_isRotation {g : EuclideanMotion Plane}
    (h : IsTranslation g) : ¬ IsRotation g :=
  fun hr => hr.2 h

/-- Every translation has determinant one. -/
theorem isTranslation_determinant (g : EuclideanMotion Plane)
    (h : IsTranslation g) :
    determinant g = 1 := by
  unfold IsTranslation at h
  rw [determinant, h]
  exact LinearMap.det_id

/-- A translation cannot be a reflection. -/
theorem isTranslation_not_isReflection {g : EuclideanMotion Plane}
    (h : IsTranslation g) : ¬ IsReflection g := by
  intro hr
  unfold IsReflection at hr
  rw [isTranslation_determinant g h] at hr
  norm_num at hr

/-- A translation cannot be a glide reflection. -/
theorem isTranslation_not_isGlideReflection {g : EuclideanMotion Plane}
    (h : IsTranslation g) : ¬ IsGlideReflection g := by
  intro hg
  unfold IsGlideReflection at hg
  rw [isTranslation_determinant g h] at hg
  norm_num at hg

/-- A rotation cannot be a reflection. -/
theorem isRotation_not_isReflection {g : EuclideanMotion Plane}
    (h : IsRotation g) : ¬ IsReflection g :=
  fun hr => (not_lt_of_ge (le_of_lt h.1)) hr.1

/-- A rotation cannot be a glide reflection. -/
theorem isRotation_not_isGlideReflection {g : EuclideanMotion Plane}
    (h : IsRotation g) : ¬ IsGlideReflection g :=
  fun hg => (not_lt_of_ge (le_of_lt h.1)) hg.1

/-- A reflection cannot be a glide reflection. -/
theorem isReflection_not_isGlideReflection {g : EuclideanMotion Plane}
    (h : IsReflection g) : ¬ IsGlideReflection g :=
  fun hg => hg.2 h.2

/--
The identity convention in one statement: the identity is a translation and is none of the other
three motion types.
-/
theorem identity_type :
    IsTranslation (1 : EuclideanMotion Plane) ∧
      ¬ IsRotation (1 : EuclideanMotion Plane) ∧
      ¬ IsReflection (1 : EuclideanMotion Plane) ∧
      ¬ IsGlideReflection (1 : EuclideanMotion Plane) := by
  have ht : IsTranslation (1 : EuclideanMotion Plane) :=
    linearPart_one
  exact ⟨ht, isTranslation_not_isRotation ht,
    isTranslation_not_isReflection ht,
    isTranslation_not_isGlideReflection ht⟩

end PlaneMotion

/-! ## Motion-type transport -/

namespace TranslationPreservingIso

variable {G H : PlaneGroup}

/--
A translation-preserving isomorphism preserves the determinant of every element's linear part.
-/
theorem map_motion_determinant (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    PlaneMotion.determinant
        ((e.toMulEquiv g : H.carrier) : EuclideanMotion Plane) =
      PlaneMotion.determinant (g : EuclideanMotion Plane) := by
  have hconj :
      ((e.realLinearEquiv.symm.trans
          (linearPart (g : EuclideanMotion Plane)).toLinearEquiv).trans
          e.realLinearEquiv) =
        (linearPart
          ((e.toMulEquiv g : H.carrier) : EuclideanMotion Plane)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro x
    have h := e.realLinearEquiv_pointAction
      (pointProjection G.carrier g) (e.realLinearEquiv.symm x)
    simpa using h
  unfold PlaneMotion.determinant
  rw [← hconj]
  simpa only [LinearEquiv.coe_det] using congrArg Units.val
    (LinearEquiv.det_conj
      (linearPart (g : EuclideanMotion Plane)).toLinearEquiv
      e.realLinearEquiv)

/-- A translation-preserving isomorphism preserves and reflects translations elementwise. -/
theorem map_isTranslation_iff (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    PlaneMotion.IsTranslation
        ((e.toMulEquiv g : H.carrier) : EuclideanMotion Plane) ↔
      PlaneMotion.IsTranslation (g : EuclideanMotion Plane) := by
  exact e.map_mem_translationSubgroup_iff g

/-- A translation-preserving isomorphism preserves and reflects rotations elementwise. -/
theorem map_isRotation_iff (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    PlaneMotion.IsRotation
        ((e.toMulEquiv g : H.carrier) : EuclideanMotion Plane) ↔
      PlaneMotion.IsRotation (g : EuclideanMotion Plane) := by
  simp only [PlaneMotion.IsRotation, e.map_motion_determinant g,
    e.map_isTranslation_iff g]

/-- A translation-preserving isomorphism preserves and reflects the square-one condition. -/
theorem map_sq_eq_one_iff (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    e.toMulEquiv g ^ 2 = 1 ↔ g ^ 2 = 1 := by
  constructor
  · intro h
    apply e.toMulEquiv.injective
    simpa using h
  · intro h
    simpa using congrArg e.toMulEquiv h

/-- The square-one condition is also preserved after coercing subgroup elements to plane motions. -/
theorem map_ambient_sq_eq_one_iff (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    (((e.toMulEquiv g : H.carrier) : EuclideanMotion Plane) ^ 2 = 1) ↔
      ((g : EuclideanMotion Plane) ^ 2 = 1) := by
  constructor
  · intro h
    have hH : e.toMulEquiv g ^ 2 = 1 := by
      apply Subtype.ext
      exact h
    exact congrArg (fun x : G.carrier => (x : EuclideanMotion Plane))
      ((e.map_sq_eq_one_iff g).mp hH)
  · intro h
    have hG : g ^ 2 = 1 := by
      apply Subtype.ext
      exact h
    exact congrArg (fun x : H.carrier => (x : EuclideanMotion Plane))
      ((e.map_sq_eq_one_iff g).mpr hG)

/-- A translation-preserving isomorphism preserves and reflects reflections elementwise. -/
theorem map_isReflection_iff (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    PlaneMotion.IsReflection
        ((e.toMulEquiv g : H.carrier) : EuclideanMotion Plane) ↔
      PlaneMotion.IsReflection (g : EuclideanMotion Plane) := by
  rw [PlaneMotion.isReflection_iff, PlaneMotion.isReflection_iff]
  rw [e.map_motion_determinant g]
  exact and_congr Iff.rfl (e.map_ambient_sq_eq_one_iff g)

/-- A translation-preserving isomorphism preserves and reflects glide reflections elementwise. -/
theorem map_isGlideReflection_iff (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    PlaneMotion.IsGlideReflection
        ((e.toMulEquiv g : H.carrier) : EuclideanMotion Plane) ↔
      PlaneMotion.IsGlideReflection (g : EuclideanMotion Plane) := by
  rw [PlaneMotion.isGlideReflection_iff,
    PlaneMotion.isGlideReflection_iff]
  rw [e.map_motion_determinant g]
  exact and_congr Iff.rfl (not_congr (e.map_ambient_sq_eq_one_iff g))

end TranslationPreservingIso

/-! ## Textbook equivalence and comparison with Version 1 -/

/--
An abstract isomorphism preserving each of the four textbook plane-motion types in both
directions.  No ambient affine map or metric-preservation condition is part of this structure.
-/
structure MotionTypePreservingIso (G H : PlaneGroup) where
  toMulEquiv : G.carrier ≃* H.carrier
  map_isTranslation_iff : ∀ g : G.carrier,
    PlaneMotion.IsTranslation (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsTranslation
        ((toMulEquiv g : H.carrier) : EuclideanMotion Plane)
  map_isRotation_iff : ∀ g : G.carrier,
    PlaneMotion.IsRotation (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsRotation
        ((toMulEquiv g : H.carrier) : EuclideanMotion Plane)
  map_isReflection_iff : ∀ g : G.carrier,
    PlaneMotion.IsReflection (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsReflection
        ((toMulEquiv g : H.carrier) : EuclideanMotion Plane)
  map_isGlideReflection_iff : ∀ g : G.carrier,
    PlaneMotion.IsGlideReflection (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsGlideReflection
        ((toMulEquiv g : H.carrier) : EuclideanMotion Plane)

namespace TranslationPreservingIso

variable {G H : PlaneGroup}

/-- Forget no data: a translation-preserving isomorphism automatically preserves all four types. -/
def toMotionTypePreservingIso (e : TranslationPreservingIso G H) :
    MotionTypePreservingIso G H where
  toMulEquiv := e.toMulEquiv
  map_isTranslation_iff g := (e.map_isTranslation_iff g).symm
  map_isRotation_iff g := (e.map_isRotation_iff g).symm
  map_isReflection_iff g := (e.map_isReflection_iff g).symm
  map_isGlideReflection_iff g := (e.map_isGlideReflection_iff g).symm

end TranslationPreservingIso

namespace MotionTypePreservingIso

variable {G H : PlaneGroup}

/--
Keeping only translation preservation turns a motion-type-preserving isomorphism into the Version 1
notion.  The other three fields are consequences rather than extra restrictions.
-/
def toTranslationPreservingIso (e : MotionTypePreservingIso G H) :
    TranslationPreservingIso G H where
  toMulEquiv := e.toMulEquiv
  map_translationSubgroup := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change PlaneMotion.IsTranslation
        (((e.toMulEquiv x : H.carrier) : EuclideanMotion Plane))
      exact (e.map_isTranslation_iff x).mp hx
    · intro hy
      have hyMotion :
          PlaneMotion.IsTranslation (y : EuclideanMotion Plane) := hy
      let x : G.carrier := e.toMulEquiv.symm y
      refine ⟨x, ?_, e.toMulEquiv.apply_symm_apply y⟩
      change PlaneMotion.IsTranslation (x : EuclideanMotion Plane)
      apply (e.map_isTranslation_iff x).mpr
      simpa [x] using hyMotion

end MotionTypePreservingIso

namespace PlaneGroup

/-- Textbook equivalence is nonempty motion-type-preserving abstract isomorphism. -/
def TextbookEquivalent (G H : PlaneGroup) : Prop :=
  Nonempty (MotionTypePreservingIso G H)

/-- Textbook equivalence is logically identical to Version 1 translation-preserving equivalence. -/
theorem textbookEquivalent_iff_equivalent (G H : PlaneGroup) :
    TextbookEquivalent G H ↔ Equivalent G H := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toTranslationPreservingIso⟩
  · rintro ⟨e⟩
    exact ⟨e.toMotionTypePreservingIso⟩

namespace TextbookEquivalent

/-- Every plane group is textbook-equivalent to itself. -/
theorem refl (G : PlaneGroup) : TextbookEquivalent G G :=
  (textbookEquivalent_iff_equivalent G G).mpr (Equivalent.refl G)

/-- Textbook equivalence is symmetric. -/
theorem symm {G H : PlaneGroup} (h : TextbookEquivalent G H) :
    TextbookEquivalent H G :=
  (textbookEquivalent_iff_equivalent H G).mpr
    (Equivalent.symm ((textbookEquivalent_iff_equivalent G H).mp h))

/-- Textbook equivalence is transitive. -/
theorem trans {G H K : PlaneGroup}
    (hGH : TextbookEquivalent G H) (hHK : TextbookEquivalent H K) :
    TextbookEquivalent G K :=
  (textbookEquivalent_iff_equivalent G K).mpr
    (Equivalent.trans
      ((textbookEquivalent_iff_equivalent G H).mp hGH)
      ((textbookEquivalent_iff_equivalent H K).mp hHK))

end TextbookEquivalent

/-- Textbook equivalence is an equivalence relation on strong plane groups. -/
theorem textbookEquivalent_equivalence : Equivalence TextbookEquivalent := by
  constructor
  · exact TextbookEquivalent.refl
  · intro G H
    exact TextbookEquivalent.symm
  · intro G H K
    exact TextbookEquivalent.trans

end PlaneGroup

/-! ## The seventeen classes under textbook equivalence -/

/--
Every strong plane group is textbook-equivalent to exactly one of the seventeen standard models.
This is obtained from `classification` solely through the logical equivalence of the two relations.
-/
theorem textbook_classification (G : PlaneGroup) :
    ∃! w : WallpaperType,
      PlaneGroup.TextbookEquivalent G (WallpaperType.model w) := by
  simpa only [PlaneGroup.textbookEquivalent_iff_equivalent] using
    classification G

end

end WallpaperGroups
