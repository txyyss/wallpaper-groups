import WallpaperGroups.Basic.EuclideanMotion

set_option linter.style.header false

/-!
# Translation vectors and translation subgroups

For a subgroup of Euclidean motions, this module provides both the additive subgroup of
translation vectors and the corresponding kernel subgroup inside the given motion group.
-/

set_option autoImplicit false

namespace WallpaperGroups
namespace EuclideanMotion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear-part homomorphism restricted to a subgroup of Euclidean motions. -/
def restrictedLinearPart (G : Subgroup (EuclideanMotion E)) : G →* (E ≃ₗᵢ[ℝ] E) :=
  linearPart.comp G.subtype

/-- Evaluating the restricted linear part agrees with the ambient linear part. -/
@[simp]
theorem restrictedLinearPart_apply (G : Subgroup (EuclideanMotion E)) (g : G) :
    restrictedLinearPart G g = linearPart (g : EuclideanMotion E) :=
  rfl

/-- Vectors whose pure translations belong to `G`. -/
def translationVectors (G : Subgroup (EuclideanMotion E)) : AddSubgroup E where
  carrier := {t | translation t ∈ G}
  zero_mem' := by simp
  add_mem' := by
    intro t u ht hu
    change translation (t + u) ∈ G
    change translation t ∈ G at ht
    change translation u ∈ G at hu
    rw [translation_add]
    exact G.mul_mem ht hu
  neg_mem' := by
    intro t ht
    change translation (-t) ∈ G
    change translation t ∈ G at ht
    rw [translation_neg]
    exact G.inv_mem ht

/-- A vector belongs to `translationVectors G` exactly when its pure translation belongs to `G`. -/
@[simp]
theorem mem_translationVectors {G : Subgroup (EuclideanMotion E)} {t : E} :
    t ∈ translationVectors G ↔ translation t ∈ G :=
  Iff.rfl

/-- A translation vector regarded as an element of the motion subgroup. -/
def translationElement (G : Subgroup (EuclideanMotion E)) (t : translationVectors G) : G :=
  ⟨translation (t : E), t.property⟩

/-- Coercing a translation element to an ambient motion recovers its pure translation. -/
@[simp]
theorem translationElement_coe (G : Subgroup (EuclideanMotion E)) (t : translationVectors G) :
    (translationElement G t : EuclideanMotion E) = translation (t : E) :=
  rfl

/-- The translation subgroup inside `G`, defined as the kernel of its linear-part map. -/
def translationSubgroup (G : Subgroup (EuclideanMotion E)) : Subgroup G :=
  (restrictedLinearPart G).ker

/-- Membership in the translation subgroup means that the ambient linear part is trivial. -/
@[simp]
theorem mem_translationSubgroup {G : Subgroup (EuclideanMotion E)} {g : G} :
    g ∈ translationSubgroup G ↔ linearPart (g : EuclideanMotion E) = 1 :=
  Iff.rfl

/-- The translation subgroup is normal because it is a kernel. -/
instance translationSubgroup_normal (G : Subgroup (EuclideanMotion E)) :
    (translationSubgroup G).Normal :=
  (restrictedLinearPart G).normal_ker

/-- A translation vector regarded as an element of the kernel translation subgroup. -/
def translationSubgroupElement (G : Subgroup (EuclideanMotion E))
    (t : translationVectors G) : translationSubgroup G :=
  ⟨translationElement G t, by
    change linearPart (translation (t : E)) = 1
    exact linearPart_translation (t : E)⟩

/-- Coercing the kernel element associated to `t` gives pure translation by `t`. -/
@[simp]
theorem translationSubgroupElement_coe_G (G : Subgroup (EuclideanMotion E))
    (t : translationVectors G) :
    ((translationSubgroupElement G t : G) : EuclideanMotion E) = translation (t : E) :=
  rfl

/-- Addition of translation vectors is multiplication of their elements in `G`. -/
theorem translationElement_add (G : Subgroup (EuclideanMotion E))
    (t u : translationVectors G) :
    translationElement G (t + u) = translationElement G t * translationElement G u := by
  apply Subtype.ext
  exact translation_add (t : E) (u : E)

/-- Addition of translation vectors is multiplication in the kernel translation subgroup. -/
theorem translationSubgroupElement_add (G : Subgroup (EuclideanMotion E))
    (t u : translationVectors G) :
    translationSubgroupElement G (t + u) =
      translationSubgroupElement G t * translationSubgroupElement G u := by
  apply Subtype.ext
  exact translationElement_add G t u

/-- Pure translations give a homomorphism from tagged translation vectors into `G`. -/
def translationElementHom (G : Subgroup (EuclideanMotion E)) :
    Multiplicative (translationVectors G) →* G where
  toFun t := translationElement G t.toAdd
  map_one' := by
    apply Subtype.ext
    exact translation_zero
  map_mul' t u := by
    change translationElement G (t.toAdd + u.toAdd) =
      translationElement G t.toAdd * translationElement G u.toAdd
    exact translationElement_add G _ _

/-- The homomorphism from tagged translation vectors into `G` is injective. -/
theorem translationElementHom_injective (G : Subgroup (EuclideanMotion E)) :
    Function.Injective (translationElementHom G) := by
  intro t u h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply translation_injective
  exact congrArg (fun x : G => (x : EuclideanMotion E)) h

/-- Pure translations give a homomorphism onto the kernel translation subgroup. -/
def translationSubgroupHom (G : Subgroup (EuclideanMotion E)) :
    Multiplicative (translationVectors G) →* translationSubgroup G where
  toFun t := translationSubgroupElement G t.toAdd
  map_one' := by
    apply Subtype.ext
    exact (translationElementHom G).map_one
  map_mul' t u := by
    apply Subtype.ext
    exact (translationElementHom G).map_mul t u

/-- The kernel-valued translation homomorphism evaluates to `translationSubgroupElement`. -/
@[simp]
theorem translationSubgroupHom_apply (G : Subgroup (EuclideanMotion E))
    (t : Multiplicative (translationVectors G)) :
    translationSubgroupHom G t = translationSubgroupElement G t.toAdd :=
  rfl

/-- The homomorphism from translation vectors to pure translations is injective. -/
theorem translationSubgroupHom_injective (G : Subgroup (EuclideanMotion E)) :
    Function.Injective (translationSubgroupHom G) := by
  intro t u h
  apply translationElementHom_injective G
  exact congrArg (fun x : translationSubgroup G => (x : G)) h

/-- A kernel element is exactly the pure translation by its translation part. -/
theorem translation_of_mem_translationSubgroup (G : Subgroup (EuclideanMotion E))
    (g : translationSubgroup G) :
    translation (translationPart ((g : G) : EuclideanMotion E)) =
      ((g : G) : EuclideanMotion E) := by
  exact (eq_translation_of_linearPart_eq_one g.property).symm

/-- The translation-vector homomorphism is onto the kernel translation subgroup. -/
theorem translationSubgroupHom_surjective (G : Subgroup (EuclideanMotion E)) :
    Function.Surjective (translationSubgroupHom G) := by
  intro g
  let t : translationVectors G :=
    ⟨translationPart ((g : G) : EuclideanMotion E), by
      change translation (translationPart ((g : G) : EuclideanMotion E)) ∈ G
      rw [translation_of_mem_translationSubgroup G g]
      exact (g : G).property⟩
  refine ⟨Multiplicative.ofAdd t, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact translation_of_mem_translationSubgroup G g

/-- Translation vectors and the kernel translation subgroup are naturally isomorphic. -/
def translationEquiv (G : Subgroup (EuclideanMotion E)) :
    Multiplicative (translationVectors G) ≃* translationSubgroup G where
  toFun := translationSubgroupHom G
  invFun g :=
    Multiplicative.ofAdd
      ⟨translationPart ((g : G) : EuclideanMotion E), by
        change translation (translationPart ((g : G) : EuclideanMotion E)) ∈ G
        rw [translation_of_mem_translationSubgroup G g]
        exact (g : G).property⟩
  left_inv t := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact translationPart_translation (t.toAdd : E)
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact translation_of_mem_translationSubgroup G g
  map_mul' := (translationSubgroupHom G).map_mul

/-- The natural equivalence sends a vector to its pure translation kernel element. -/
@[simp]
theorem translationEquiv_apply (G : Subgroup (EuclideanMotion E))
    (t : Multiplicative (translationVectors G)) :
    translationEquiv G t = translationSubgroupElement G t.toAdd :=
  rfl

/-- The inverse equivalence recovers the translation part of a kernel element. -/
@[simp]
theorem translationEquiv_symm_apply_coe (G : Subgroup (EuclideanMotion E))
    (g : translationSubgroup G) :
    (((translationEquiv G).symm g).toAdd : E) =
      translationPart ((g : G) : EuclideanMotion E) :=
  rfl

/-- Membership in the kernel is equivalent to being a pure translation from `G`. -/
theorem mem_translationSubgroup_iff_exists (G : Subgroup (EuclideanMotion E)) (g : G) :
    g ∈ translationSubgroup G ↔
      ∃ t : translationVectors G, (g : EuclideanMotion E) = translation (t : E) := by
  constructor
  · intro hg
    let g' : translationSubgroup G := ⟨g, hg⟩
    let t : translationVectors G :=
      ⟨translationPart (g : EuclideanMotion E), by
        change translation (translationPart (g : EuclideanMotion E)) ∈ G
        rw [translation_of_mem_translationSubgroup G g']
        exact g.property⟩
    exact ⟨t, (translation_of_mem_translationSubgroup G g').symm⟩
  · rintro ⟨t, hgt⟩
    rw [mem_translationSubgroup, hgt]
    exact linearPart_translation (t : E)

end

end EuclideanMotion
end WallpaperGroups
