import WallpaperGroups.Invariants.Translation

set_option linter.style.header false

/-!
# Point groups and their action on translations

The point group of a Euclidean-motion subgroup is the range of its restricted linear-part map.
Its action on translation vectors is the underlying linear-isometry action; well-definedness is
proved geometrically by conjugating pure translations by a lift in the motion subgroup.
-/

set_option autoImplicit false

namespace WallpaperGroups
namespace EuclideanMotion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The point group of `G`, defined as the range of its restricted linear-part homomorphism. -/
def pointGroup (G : Subgroup (EuclideanMotion E)) : Subgroup (E ≃ₗᵢ[ℝ] E) :=
  (restrictedLinearPart G).range

/-- The canonical projection from a motion subgroup onto its point group. -/
def pointProjection (G : Subgroup (EuclideanMotion E)) : G →* pointGroup G :=
  (restrictedLinearPart G).rangeRestrict

/-- Coercing a projected point-group element gives the original motion's linear part. -/
@[simp]
theorem pointProjection_coe (G : Subgroup (EuclideanMotion E)) (g : G) :
    (pointProjection G g : E ≃ₗᵢ[ℝ] E) = linearPart (g : EuclideanMotion E) :=
  rfl

/-- The linear part of every element of `G` lies in its point group. -/
theorem linearPart_mem_pointGroup (G : Subgroup (EuclideanMotion E)) (g : G) :
    linearPart (g : EuclideanMotion E) ∈ pointGroup G :=
  ⟨g, rfl⟩

/-- Membership in the point group is witnessed by a lift in `G`. -/
theorem mem_pointGroup_iff (G : Subgroup (EuclideanMotion E)) (A : E ≃ₗᵢ[ℝ] E) :
    A ∈ pointGroup G ↔ ∃ g : G, linearPart (g : EuclideanMotion E) = A :=
  Iff.rfl

/-- Every point-group element has a lift in the original motion subgroup. -/
theorem pointGroup_exists_lift (G : Subgroup (EuclideanMotion E)) (h : pointGroup G) :
    ∃ g : G, linearPart (g : EuclideanMotion E) = (h : E ≃ₗᵢ[ℝ] E) :=
  h.property

/-- The point projection is surjective by construction. -/
theorem pointProjection_surjective (G : Subgroup (EuclideanMotion E)) :
    Function.Surjective (pointProjection G) :=
  (restrictedLinearPart G).rangeRestrict_surjective

/-- The point projection has exactly the translation subgroup as its kernel. -/
theorem pointProjection_ker (G : Subgroup (EuclideanMotion E)) :
    (pointProjection G).ker = translationSubgroup G := by
  change (restrictedLinearPart G).rangeRestrict.ker = (restrictedLinearPart G).ker
  exact MonoidHom.ker_rangeRestrict (restrictedLinearPart G)

/-- A point-group linear isometry preserves the additive subgroup of translation vectors. -/
theorem pointGroup_apply_mem_translationVectors (G : Subgroup (EuclideanMotion E))
    (h : pointGroup G) (t : translationVectors G) :
    (h : E ≃ₗᵢ[ℝ] E) (t : E) ∈ translationVectors G := by
  rcases pointGroup_exists_lift G h with ⟨g, hg⟩
  change translation ((h : E ≃ₗᵢ[ℝ] E) (t : E)) ∈ G
  rw [← hg, ← conjugate_translation]
  exact G.mul_mem (G.mul_mem g.property t.property) (G.inv_mem g.property)

/-- A point-group element as an additive automorphism of the translation vectors. -/
def pointAction (G : Subgroup (EuclideanMotion E)) (h : pointGroup G) :
    AddAut (translationVectors G) where
  toFun t := ⟨(h : E ≃ₗᵢ[ℝ] E) (t : E), pointGroup_apply_mem_translationVectors G h t⟩
  invFun t :=
    ⟨(h : E ≃ₗᵢ[ℝ] E)⁻¹ (t : E), by
      simpa using pointGroup_apply_mem_translationVectors G h⁻¹ t⟩
  left_inv t := by
    apply Subtype.ext
    exact (h : E ≃ₗᵢ[ℝ] E).symm_apply_apply (t : E)
  right_inv t := by
    apply Subtype.ext
    exact (h : E ≃ₗᵢ[ℝ] E).apply_symm_apply (t : E)
  map_add' t u := by
    apply Subtype.ext
    exact map_add (h : E ≃ₗᵢ[ℝ] E) (t : E) (u : E)

/-- The underlying vector of `pointAction` is the point-group linear isometry applied to it. -/
@[simp]
theorem pointAction_coe (G : Subgroup (EuclideanMotion E)) (h : pointGroup G)
    (t : translationVectors G) :
    (pointAction G h t : E) = (h : E ≃ₗᵢ[ℝ] E) (t : E) :=
  rfl

/-- The identity point-group element acts trivially. -/
@[simp]
theorem pointAction_one (G : Subgroup (EuclideanMotion E)) (t : translationVectors G) :
    pointAction G 1 t = t := by
  apply Subtype.ext
  rfl

/-- Point-group multiplication acts by composition in the same order. -/
theorem pointAction_mul (G : Subgroup (EuclideanMotion E)) (h k : pointGroup G)
    (t : translationVectors G) :
    pointAction G (h * k) t = pointAction G h (pointAction G k t) := by
  apply Subtype.ext
  rfl

/-- The point action preserves addition of translation vectors. -/
@[simp]
theorem pointAction_add (G : Subgroup (EuclideanMotion E)) (h : pointGroup G)
    (t u : translationVectors G) :
    pointAction G h (t + u) = pointAction G h t + pointAction G h u :=
  (pointAction G h).map_add t u

/-- The point action preserves negation of translation vectors. -/
@[simp]
theorem pointAction_neg (G : Subgroup (EuclideanMotion E)) (h : pointGroup G)
    (t : translationVectors G) :
    pointAction G h (-t) = -pointAction G h t :=
  (pointAction G h).map_neg t

/-- The point action, bundled as a homomorphism into additive automorphisms under composition. -/
def pointActionHom (G : Subgroup (EuclideanMotion E)) :
    pointGroup G →* Multiplicative (AddAut (translationVectors G)) where
  toFun h := Multiplicative.ofAdd (pointAction G h)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    exact pointAction_one G
  map_mul' h k := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    exact pointAction_mul G h k

/-- Evaluating the bundled action homomorphism recovers the explicit additive automorphism. -/
@[simp]
theorem pointActionHom_apply (G : Subgroup (EuclideanMotion E)) (h : pointGroup G) :
    (pointActionHom G h).toAdd = pointAction G h :=
  rfl

/-- The action of the point represented by `g` is its ordinary linear-part action. -/
@[simp]
theorem pointAction_projection_coe (G : Subgroup (EuclideanMotion E)) (g : G)
    (t : translationVectors G) :
    (pointAction G (pointProjection G g) t : E) =
      linearPart (g : EuclideanMotion E) (t : E) :=
  rfl

end

end EuclideanMotion
end WallpaperGroups
