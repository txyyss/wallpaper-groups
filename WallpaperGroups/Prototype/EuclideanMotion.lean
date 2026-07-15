import WallpaperGroups.Invariants.ExactSequence

set_option linter.style.header false

/-!
# Euclidean-motion regression tests

The M0 prototype has been migrated to the production M1 API.  This file now keeps compiling
examples for the core motion formulas and the translation--point-group exact sequence; production
modules never import it.
-/

set_option autoImplicit false

namespace WallpaperGroups.Prototype

open WallpaperGroups.EuclideanMotion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example (t u : E) : translation (t + u) = translation t * translation u :=
  translation_add t u

example (g : EuclideanMotion E) (x : E) :
    g x = translationPart g + linearPart g x :=
  apply_eq_translationPart_add g x

example (g : EuclideanMotion E) (t : E) :
    g * translation t * g⁻¹ = translation (linearPart g t) :=
  conjugate_translation g t

variable (G : Subgroup (EuclideanMotion E))

example (t : translationVectors G) : translationElement G t ∈ translationSubgroup G := by
  rw [mem_translationSubgroup]
  exact linearPart_translation (t : E)

example (h : pointGroup G) :
    ∃ g : G, linearPart (g : EuclideanMotion E) = (h : E ≃ₗᵢ[ℝ] E) :=
  pointGroup_exists_lift G h

example (h : pointGroup G) (t : translationVectors G) :
    (pointAction G h t : E) ∈ translationVectors G :=
  (pointAction G h t).property

example : (translationSubgroup G).Normal :=
  inferInstance

example : (translationInclusion G).range = (pointProjection G).ker :=
  translationInclusion_range_eq_pointProjection_ker G

example (g : G) (t : translationVectors G) :
    g * translationElement G t * g⁻¹ =
      translationElement G (pointAction G (pointProjection G g) t) :=
  conjugate_translationElement G g t

end

end WallpaperGroups.Prototype
