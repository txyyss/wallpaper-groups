import Mathlib.GroupTheory.GroupExtension.Defs
import WallpaperGroups.Invariants.PointGroup

set_option linter.style.header false

/-!
# The translation--point-group exact sequence

For every subgroup `G` of Euclidean motions, its translation kernel, `G`, and its point group form
a mathlib `GroupExtension`.  The module also keeps a geometric conjugation theorem alongside the
abstract kernel/range interface.
-/

set_option autoImplicit false

namespace WallpaperGroups
namespace EuclideanMotion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Inclusion of the translation subgroup into the original motion subgroup. -/
def translationInclusion (G : Subgroup (EuclideanMotion E)) : translationSubgroup G →* G :=
  (translationSubgroup G).subtype

/-- The translation inclusion is the ordinary subtype coercion. -/
@[simp]
theorem translationInclusion_apply (G : Subgroup (EuclideanMotion E))
    (t : translationSubgroup G) : translationInclusion G t = (t : G) :=
  rfl

/-- The translation-subgroup inclusion is injective. -/
theorem translationInclusion_injective (G : Subgroup (EuclideanMotion E)) :
    Function.Injective (translationInclusion G) :=
  (translationSubgroup G).subtype_injective

/-- Exactness at `G`: the translation inclusion range is the point-projection kernel. -/
theorem translationInclusion_range_eq_pointProjection_ker
    (G : Subgroup (EuclideanMotion E)) :
    (translationInclusion G).range = (pointProjection G).ker := by
  rw [translationInclusion, Subgroup.range_subtype, pointProjection_ker]

/-- The canonical short exact sequence `1 → T(G) → G → H(G) → 1`. -/
def pointGroupExtension (G : Subgroup (EuclideanMotion E)) :
    GroupExtension (translationSubgroup G) G (pointGroup G) where
  inl := translationInclusion G
  rightHom := pointProjection G
  inl_injective := translationInclusion_injective G
  range_inl_eq_ker_rightHom := translationInclusion_range_eq_pointProjection_ker G
  rightHom_surjective := pointProjection_surjective G

/-- The extension's left map is the translation-subgroup inclusion. -/
@[simp]
theorem pointGroupExtension_inl (G : Subgroup (EuclideanMotion E))
    (t : translationSubgroup G) : (pointGroupExtension G).inl t = (t : G) :=
  rfl

/-- The extension's right map is the canonical point projection. -/
@[simp]
theorem pointGroupExtension_rightHom (G : Subgroup (EuclideanMotion E)) (g : G) :
    (pointGroupExtension G).rightHom g = pointProjection G g :=
  rfl

/-- The kernel translation subgroup is normal in `G`. -/
theorem translationSubgroup_isNormal (G : Subgroup (EuclideanMotion E)) :
    (translationSubgroup G).Normal :=
  inferInstance

/-- Geometric conjugation of a translation vector by an element of `G`. -/
theorem conjugate_translationVector (G : Subgroup (EuclideanMotion E)) (g : G)
    (t : translationVectors G) :
    (g : EuclideanMotion E) * translation (t : E) * (g : EuclideanMotion E)⁻¹ =
      translation ((pointAction G (pointProjection G g) t : translationVectors G) : E) := by
  rw [conjugate_translation]
  rfl

/-- The same conjugation formula expressed entirely inside the subgroup `G`. -/
theorem conjugate_translationElement (G : Subgroup (EuclideanMotion E)) (g : G)
    (t : translationVectors G) :
    g * translationElement G t * g⁻¹ =
      translationElement G (pointAction G (pointProjection G g) t) := by
  apply Subtype.ext
  exact conjugate_translationVector G g t

/-- The abstract conjugation action of the extension agrees with the geometric point action. -/
theorem pointGroupExtension_conjAct_translationSubgroupElement
    (G : Subgroup (EuclideanMotion E)) (g : G) (t : translationVectors G) :
    (pointGroupExtension G).conjAct g (translationSubgroupElement G t) =
      translationSubgroupElement G (pointAction G (pointProjection G g) t) := by
  apply (pointGroupExtension G).inl_injective
  rw [(pointGroupExtension G).inl_conjAct_comm]
  exact conjugate_translationElement G g t

end

end EuclideanMotion
end WallpaperGroups
