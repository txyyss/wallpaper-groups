module

public import WallpaperGroups.Extensions.PointGroup
public import WallpaperGroups.Presentations.DihedralExtension

set_option linter.style.header false

/-!
# Existing dihedral factors as normalized cocycles

This adapter checks the new sign and multiplication conventions against the normalized section
already used in the Version 1 multiple-reflection classification.  It does not change or replace
that classification code.
-/

public section

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

private theorem pointGroupExtensionOverAction_rightHom
    (G : Subgroup (EuclideanMotion Plane)) (g : G) :
    (pointGroupExtensionOverAction G).toGroupExtension.rightHom g =
      pointProjection G g := by
  rw [pointGroupExtensionOverAction_toGroupExtension,
    pointGroupVectorExtension_rightHom]

private theorem pointGroupExtensionOverAction_inl
    (G : Subgroup (EuclideanMotion Plane))
    (t : Multiplicative (translationVectors G)) :
    (pointGroupExtensionOverAction G).toGroupExtension.inl t =
      translationElement G t.toAdd := by
  rw [pointGroupExtensionOverAction_toGroupExtension,
    pointGroupVectorExtension_inl]

/-- A `DihedralExtensionData` lift, viewed as a normalized section of the canonical point-group
extension with translation-vector kernel. -/
@[expose] def dihedralNormalizedSection {G : PlaneGroup}
    (c : DihedralExtensionData G) :
    NormalizedSection
      (pointGroupExtensionOverAction G.carrier).toGroupExtension where
  toSection :=
    { toFun := c.lift
      rightInverse_rightHom := by
        intro q
        rw [pointGroupExtensionOverAction_rightHom]
        exact c.lift_projection q }
  map_one := c.lift_one

/-- The generic section factor is the existing Version 1 `dihedralFactor`. -/
theorem dihedralNormalizedSection_factor {G : PlaneGroup}
    (c : DihedralExtensionData G)
    (q r : pointGroup G.carrier) :
    NormalizedSection.factor (dihedralNormalizedSection c) q r =
      dihedralFactor c q r := by
  apply (NormalizedSection.factor_eq_iff
    (dihedralNormalizedSection c) q r (dihedralFactor c q r)).2
  rw [pointGroupExtensionOverAction_inl]
  change
    translationElement G.carrier (dihedralFactor c q r) =
      c.lift q * c.lift r * (c.lift (q * r))⁻¹
  rw [dihedralLift_mul_lift]
  group

/-- The normalized cocycle extracted from the existing dihedral section. -/
noncomputable def dihedralNormalizedCocycle {G : PlaneGroup}
    (c : DihedralExtensionData G) :
    NormalizedCocycle (pointActionHom G.carrier) :=
  (dihedralNormalizedSection c).toCocycle
    (pointGroupExtensionOverAction G.carrier)

@[simp]
theorem dihedralNormalizedCocycle_apply {G : PlaneGroup}
    (c : DihedralExtensionData G)
    (q r : pointGroup G.carrier) :
    dihedralNormalizedCocycle c q r =
      dihedralFactor c q r :=
  by
    simpa only [dihedralNormalizedCocycle,
      NormalizedSection.toCocycle_apply] using
      dihedralNormalizedSection_factor c q r

/-- The existing dihedral factor table satisfies the generic cocycle identity. -/
theorem dihedralFactor_cocycle {G : PlaneGroup}
    (c : DihedralExtensionData G)
    (q r s : pointGroup G.carrier) :
    dihedralFactor c q r + dihedralFactor c (q * r) s =
      pointAction G.carrier q (dihedralFactor c r s) +
        dihedralFactor c q (r * s) := by
  change
    dihedralFactor c q r + dihedralFactor c (q * r) s =
      AdditiveAction.apply (pointActionHom G.carrier) q
          (dihedralFactor c r s) +
        dihedralFactor c q (r * s)
  simpa only [dihedralNormalizedCocycle_apply] using
    (dihedralNormalizedCocycle c).cocycle q r s

end

end WallpaperGroups
