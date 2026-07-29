import WallpaperGroups.Extensions.Section
import WallpaperGroups.Invariants.ExactSequence

set_option linter.style.header false

/-!
# The translation--point-group extension over its explicit action

This is a thin adapter from the existing canonical `pointGroupExtension` to the
dimension-independent explicit cocycle API.  It only relabels the kernel through
`translationEquiv`; no short exact sequence or geometric invariant is redefined.
-/

set_option autoImplicit false

namespace WallpaperGroups
namespace EuclideanMotion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical point-group extension with its kernel endpoint expressed directly as additive
translation vectors in multiplicative notation. -/
def pointGroupVectorExtension (G : Subgroup (EuclideanMotion E)) :
    GroupExtension (Multiplicative (translationVectors G)) G (pointGroup G) :=
  WallpaperGroups.GroupExtension.relabelKernel
    (pointGroupExtension G) (translationEquiv G)

@[simp]
theorem pointGroupVectorExtension_inl
    (G : Subgroup (EuclideanMotion E))
    (t : Multiplicative (translationVectors G)) :
    (pointGroupVectorExtension G).inl t =
      translationElement G t.toAdd :=
  rfl

@[simp]
theorem pointGroupVectorExtension_rightHom
    (G : Subgroup (EuclideanMotion E)) (g : G) :
    (pointGroupVectorExtension G).rightHom g =
      pointProjection G g :=
  rfl

/-- The canonical translation--point-group extension realizes `pointActionHom` by conjugation. -/
def pointGroupExtensionOverAction (G : Subgroup (EuclideanMotion E)) :
    ExtensionOverAction (E := G) (pointActionHom G) where
  toGroupExtension := pointGroupVectorExtension G
  conjugation_inl := by
    intro g t
    change
      translationElement G
          (pointAction G (pointProjection G g) t) =
        g * translationElement G t * g⁻¹
    exact (conjugate_translationElement G g t).symm

end

end EuclideanMotion
end WallpaperGroups
