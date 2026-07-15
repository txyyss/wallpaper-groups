import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.QuotientGroup.Basic
import WallpaperGroups.Basic.PlaneGroup

set_option linter.style.header false

/-!
# Translation-preserving equivalences of plane groups

The classification identifies plane groups by abstract group isomorphisms that carry the full
translation subgroup onto the full translation subgroup.  This file packages that relation and
derives its canonical maps on translation vectors, stored lattices, and point groups.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/--
An abstract group isomorphism between plane groups that maps the full translation subgroup of the
source onto the full translation subgroup of the target.
-/
structure TranslationPreservingIso (G H : PlaneGroup) where
  toMulEquiv : G.carrier ≃* H.carrier
  map_translationSubgroup :
    (translationSubgroup G.carrier).map toMulEquiv.toMonoidHom =
      translationSubgroup H.carrier

namespace TranslationPreservingIso

variable {G H K L : PlaneGroup}

/-- Translation-preserving isomorphisms are equal when their underlying group isomorphisms agree. -/
@[ext]
theorem ext {e f : TranslationPreservingIso G H}
    (h : e.toMulEquiv = f.toMulEquiv) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- The inverse group isomorphism maps the target translation subgroup back to the source. -/
theorem map_translationSubgroup_symm (e : TranslationPreservingIso G H) :
    (translationSubgroup H.carrier).map e.toMulEquiv.symm.toMonoidHom =
      translationSubgroup G.carrier :=
  (Subgroup.map_symm_eq_iff_map_eq
    (K := translationSubgroup G.carrier)).mpr e.map_translationSubgroup

/-- Pulling back the target translation subgroup recovers the source translation subgroup. -/
theorem comap_translationSubgroup (e : TranslationPreservingIso G H) :
    (translationSubgroup H.carrier).comap e.toMulEquiv.toMonoidHom =
      translationSubgroup G.carrier := by
  rw [← e.map_translationSubgroup]
  exact Subgroup.comap_map_eq_self_of_injective e.toMulEquiv.injective _

/-- An element maps into the target translation subgroup exactly when it is a source translation. -/
@[simp]
theorem map_mem_translationSubgroup_iff (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    e.toMulEquiv g ∈ translationSubgroup H.carrier ↔
      g ∈ translationSubgroup G.carrier := by
  rw [← e.map_translationSubgroup]
  exact Subgroup.mem_map_iff_mem e.toMulEquiv.injective

/-- The image of a pure translation lies in the target translation subgroup. -/
theorem map_translationElement_mem (e : TranslationPreservingIso G H)
    (t : translationVectors G.carrier) :
    e.toMulEquiv (translationElement G.carrier t) ∈
      translationSubgroup H.carrier := by
  rw [e.map_mem_translationSubgroup_iff]
  change linearPart (translation (t : Plane)) = 1
  exact linearPart_translation _

/-- Identity isomorphism of a plane group, preserving translations. -/
def refl (G : PlaneGroup) : TranslationPreservingIso G G where
  toMulEquiv := MulEquiv.refl G.carrier
  map_translationSubgroup := Subgroup.map_id _

/-- Inverse of a translation-preserving isomorphism. -/
def symm (e : TranslationPreservingIso G H) : TranslationPreservingIso H G where
  toMulEquiv := e.toMulEquiv.symm
  map_translationSubgroup := e.map_translationSubgroup_symm

/-- Composition of translation-preserving isomorphisms. -/
def trans (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    TranslationPreservingIso G K where
  toMulEquiv := e.toMulEquiv.trans f.toMulEquiv
  map_translationSubgroup := by
    change (translationSubgroup G.carrier).map
      (f.toMulEquiv.toMonoidHom.comp e.toMulEquiv.toMonoidHom) =
        translationSubgroup K.carrier
    rw [← Subgroup.map_map, e.map_translationSubgroup, f.map_translationSubgroup]

/-- Taking the inverse twice returns the original translation-preserving isomorphism. -/
@[simp]
theorem symm_symm (e : TranslationPreservingIso G H) : e.symm.symm = e := by
  apply ext
  rfl

/-- The identity translation-preserving isomorphism is a left unit. -/
@[simp]
theorem refl_trans (e : TranslationPreservingIso G H) : (refl G).trans e = e := by
  apply ext
  apply MulEquiv.ext
  intro g
  rfl

/-- The identity translation-preserving isomorphism is a right unit. -/
@[simp]
theorem trans_refl (e : TranslationPreservingIso G H) : e.trans (refl H) = e := by
  apply ext
  apply MulEquiv.ext
  intro g
  rfl

/-- Composition of translation-preserving isomorphisms is associative. -/
theorem trans_assoc (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K)
    (k : TranslationPreservingIso K L) :
    (e.trans f).trans k = e.trans (f.trans k) := by
  apply ext
  apply MulEquiv.ext
  intro g
  rfl

/-- A translation-preserving isomorphism followed by its inverse is the identity. -/
@[simp]
theorem trans_symm (e : TranslationPreservingIso G H) : e.trans e.symm = refl G := by
  apply ext
  exact e.toMulEquiv.self_trans_symm

/-- The inverse followed by the original translation-preserving isomorphism is the identity. -/
@[simp]
theorem symm_trans (e : TranslationPreservingIso G H) : e.symm.trans e = refl H := by
  apply ext
  exact e.toMulEquiv.symm_trans_self

/-- Restrict a translation-preserving isomorphism to the two kernel translation subgroups. -/
def translationSubgroupEquiv (e : TranslationPreservingIso G H) :
    translationSubgroup G.carrier ≃* translationSubgroup H.carrier :=
  (e.toMulEquiv.subgroupMap (translationSubgroup G.carrier)).trans
    (MulEquiv.subgroupCongr e.map_translationSubgroup)

/-- Restriction to translation subgroups has the same underlying group map. -/
@[simp]
theorem translationSubgroupEquiv_coe (e : TranslationPreservingIso G H)
    (t : translationSubgroup G.carrier) :
    ((e.translationSubgroupEquiv t : translationSubgroup H.carrier) : H.carrier) =
      e.toMulEquiv (t : G.carrier) :=
  rfl

/-- The square formed by the two translation inclusions and the restricted equivalence commutes. -/
theorem translationSubgroupEquiv_inclusion_commutes (e : TranslationPreservingIso G H) :
    (translationSubgroup H.carrier).subtype.comp
        e.translationSubgroupEquiv.toMonoidHom =
      e.toMulEquiv.toMonoidHom.comp (translationSubgroup G.carrier).subtype := by
  apply MonoidHom.ext
  intro t
  rfl

/-- Restriction of the identity isomorphism is the identity on translations. -/
@[simp]
theorem translationSubgroupEquiv_refl :
    (refl G).translationSubgroupEquiv =
      MulEquiv.refl (translationSubgroup G.carrier) := by
  ext t
  rfl

/-- Restriction commutes with taking inverses. -/
@[simp]
theorem translationSubgroupEquiv_symm (e : TranslationPreservingIso G H) :
    e.symm.translationSubgroupEquiv = e.translationSubgroupEquiv.symm := by
  ext t
  rfl

/-- Restriction commutes with composition. -/
@[simp]
theorem translationSubgroupEquiv_trans
    (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    (e.trans f).translationSubgroupEquiv =
      e.translationSubgroupEquiv.trans f.translationSubgroupEquiv := by
  ext t
  rfl

/-- The induced isomorphism between the multiplicatively tagged translation-vector groups. -/
def translationVectorMulEquiv (e : TranslationPreservingIso G H) :
    Multiplicative (translationVectors G.carrier) ≃*
      Multiplicative (translationVectors H.carrier) :=
  (translationEquiv G.carrier).trans
    (e.translationSubgroupEquiv.trans (translationEquiv H.carrier).symm)

/-- The induced additive equivalence between the full groups of translation vectors. -/
def translationVectorEquiv (e : TranslationPreservingIso G H) :
    translationVectors G.carrier ≃+ translationVectors H.carrier :=
  AddEquiv.toMultiplicative.symm e.translationVectorMulEquiv

/-- Additivizing the tagged equivalence recovers `translationVectorEquiv`. -/
theorem translationVectorEquiv_toMultiplicative (e : TranslationPreservingIso G H) :
    AddEquiv.toMultiplicative e.translationVectorEquiv = e.translationVectorMulEquiv :=
  AddEquiv.toMultiplicative.apply_symm_apply e.translationVectorMulEquiv

/-- The tagged and additive translation-vector maps have the same underlying function. -/
@[simp]
theorem translationVectorMulEquiv_apply_toAdd (e : TranslationPreservingIso G H)
    (t : Multiplicative (translationVectors G.carrier)) :
    (e.translationVectorMulEquiv t).toAdd = e.translationVectorEquiv t.toAdd :=
  rfl

/-- The abstract group isomorphism carries each pure translation to the induced target vector. -/
theorem map_translationElement (e : TranslationPreservingIso G H)
    (t : translationVectors G.carrier) :
    e.toMulEquiv (translationElement G.carrier t) =
      translationElement H.carrier (e.translationVectorEquiv t) := by
  have h := (translationEquiv H.carrier).apply_symm_apply
    (e.translationSubgroupEquiv
      (translationEquiv G.carrier (Multiplicative.ofAdd t)))
  have hc := congrArg
    (fun x : translationSubgroup H.carrier => (x : H.carrier)) h
  exact hc.symm

/-- Ambiently, the image of translation by `t` is translation by the induced vector. -/
theorem map_pureTranslation (e : TranslationPreservingIso G H)
    (t : translationVectors G.carrier) :
    ((e.toMulEquiv (translationElement G.carrier t) : H.carrier) :
        EuclideanMotion Plane) =
      translation (e.translationVectorEquiv t : Plane) := by
  rw [e.map_translationElement]
  rfl

/-- The induced map sends the zero translation vector to zero. -/
@[simp]
theorem translationVectorEquiv_zero (e : TranslationPreservingIso G H) :
    e.translationVectorEquiv 0 = 0 :=
  map_zero e.translationVectorEquiv

/-- The induced map preserves addition of translation vectors. -/
@[simp]
theorem translationVectorEquiv_add (e : TranslationPreservingIso G H)
    (t u : translationVectors G.carrier) :
    e.translationVectorEquiv (t + u) =
      e.translationVectorEquiv t + e.translationVectorEquiv u :=
  map_add e.translationVectorEquiv t u

/-- The induced map preserves negation of translation vectors. -/
@[simp]
theorem translationVectorEquiv_neg (e : TranslationPreservingIso G H)
    (t : translationVectors G.carrier) :
    e.translationVectorEquiv (-t) = -e.translationVectorEquiv t :=
  map_neg e.translationVectorEquiv t

/-- The identity plane-group isomorphism induces the identity on translation vectors. -/
@[simp]
theorem translationVectorEquiv_refl :
    (refl G).translationVectorEquiv = AddEquiv.refl (translationVectors G.carrier) := by
  apply AddEquiv.ext
  intro t
  apply Subtype.ext
  apply translation_injective
  change translation ((refl G).translationVectorEquiv t : Plane) = translation (t : Plane)
  have h := congrArg (fun g : G.carrier => (g : EuclideanMotion Plane))
    ((refl G).map_translationElement t)
  exact h.symm

/-- The inverse plane-group isomorphism induces the inverse translation-vector equivalence. -/
@[simp]
theorem translationVectorEquiv_symm (e : TranslationPreservingIso G H) :
    e.symm.translationVectorEquiv = e.translationVectorEquiv.symm := by
  apply AddEquiv.ext
  intro t
  apply e.translationVectorEquiv.injective
  rw [e.translationVectorEquiv.apply_symm_apply]
  apply Subtype.ext
  apply translation_injective
  calc
    translation (e.translationVectorEquiv (e.symm.translationVectorEquiv t) : Plane) =
        ((e.toMulEquiv
          (translationElement G.carrier (e.symm.translationVectorEquiv t)) : H.carrier) :
            EuclideanMotion Plane) :=
      (e.map_pureTranslation (e.symm.translationVectorEquiv t)).symm
    _ = ((e.toMulEquiv
          (e.toMulEquiv.symm (translationElement H.carrier t)) : H.carrier) :
            EuclideanMotion Plane) := by
      rw [← e.symm.map_translationElement]
      rfl
    _ = translation (t : Plane) := by
      rw [e.toMulEquiv.apply_symm_apply]
      rfl

/-- Composition of plane-group isomorphisms induces composition on translation vectors. -/
@[simp]
theorem translationVectorEquiv_trans
    (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    (e.trans f).translationVectorEquiv =
      e.translationVectorEquiv.trans f.translationVectorEquiv := by
  apply AddEquiv.ext
  intro t
  apply Subtype.ext
  apply translation_injective
  have h := congrArg f.toMulEquiv (e.map_translationElement t)
  calc
    translation (((e.trans f).translationVectorEquiv t :
      translationVectors K.carrier) : Plane) =
        (((e.trans f).toMulEquiv (translationElement G.carrier t) : K.carrier) :
          EuclideanMotion Plane) := ((e.trans f).map_pureTranslation t).symm
    _ = ((f.toMulEquiv (translationElement H.carrier (e.translationVectorEquiv t)) :
          K.carrier) : EuclideanMotion Plane) := by
            exact congrArg (fun g : K.carrier => (g : EuclideanMotion Plane)) h
    _ = translation (f.translationVectorEquiv (e.translationVectorEquiv t) : Plane) :=
      f.map_pureTranslation (e.translationVectorEquiv t)

/-- The tagged translation-vector construction sends identity to identity. -/
@[simp]
theorem translationVectorMulEquiv_refl :
    (refl G).translationVectorMulEquiv =
      MulEquiv.refl (Multiplicative (translationVectors G.carrier)) := by
  apply MulEquiv.ext
  intro t
  apply Multiplicative.toAdd.injective
  change (refl G).translationVectorEquiv t.toAdd = t.toAdd
  rw [translationVectorEquiv_refl]
  rfl

/-- The tagged translation-vector construction commutes with inverses. -/
@[simp]
theorem translationVectorMulEquiv_symm (e : TranslationPreservingIso G H) :
    e.symm.translationVectorMulEquiv = e.translationVectorMulEquiv.symm := by
  apply MulEquiv.ext
  intro t
  apply Multiplicative.toAdd.injective
  change e.symm.translationVectorEquiv t.toAdd = e.translationVectorEquiv.symm t.toAdd
  rw [translationVectorEquiv_symm]

/-- The tagged translation-vector construction commutes with composition. -/
@[simp]
theorem translationVectorMulEquiv_trans
    (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    (e.trans f).translationVectorMulEquiv =
      e.translationVectorMulEquiv.trans f.translationVectorMulEquiv := by
  apply MulEquiv.ext
  intro t
  apply Multiplicative.toAdd.injective
  change (e.trans f).translationVectorEquiv t.toAdd =
    f.translationVectorEquiv (e.translationVectorEquiv t.toAdd)
  rw [translationVectorEquiv_trans]
  rfl

/-- The induced integer-linear equivalence between the two stored lattice carriers. -/
def translationLatticeEquiv (e : TranslationPreservingIso G H) :
    G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier :=
  G.translationLattice.equivOfAddEquiv H.translationLattice
    (G.latticeTranslationEquiv.trans
      (e.translationVectorEquiv.trans H.latticeTranslationEquiv.symm))

/--
The lattice equivalence agrees with the translation-vector equivalence under carrier adapters.
-/
@[simp]
theorem latticeTranslationEquiv_translationLatticeEquiv
    (e : TranslationPreservingIso G H) (t : G.translationLattice.carrier) :
    H.latticeTranslationEquiv (e.translationLatticeEquiv t) =
      e.translationVectorEquiv (G.latticeTranslationEquiv t) := by
  change H.latticeTranslationEquiv
      (H.latticeTranslationEquiv.symm
        (e.translationVectorEquiv (G.latticeTranslationEquiv t))) = _
  exact H.latticeTranslationEquiv.apply_symm_apply _

/-- The identity plane-group isomorphism induces the identity stored-lattice equivalence. -/
@[simp]
theorem translationLatticeEquiv_refl :
    (refl G).translationLatticeEquiv =
      LinearEquiv.refl ℤ G.translationLattice.carrier := by
  apply LinearEquiv.ext
  intro t
  apply G.latticeTranslationEquiv.injective
  simp

/-- The induced stored-lattice equivalence sends zero to zero. -/
@[simp]
theorem translationLatticeEquiv_zero (e : TranslationPreservingIso G H) :
    e.translationLatticeEquiv 0 = 0 :=
  map_zero e.translationLatticeEquiv

/-- The induced stored-lattice equivalence preserves addition. -/
@[simp]
theorem translationLatticeEquiv_add (e : TranslationPreservingIso G H)
    (t u : G.translationLattice.carrier) :
    e.translationLatticeEquiv (t + u) =
      e.translationLatticeEquiv t + e.translationLatticeEquiv u :=
  map_add e.translationLatticeEquiv t u

/-- The induced stored-lattice equivalence preserves negation. -/
@[simp]
theorem translationLatticeEquiv_neg (e : TranslationPreservingIso G H)
    (t : G.translationLattice.carrier) :
    e.translationLatticeEquiv (-t) = -e.translationLatticeEquiv t :=
  map_neg e.translationLatticeEquiv t

/-- Taking inverses is consistent for the induced stored-lattice equivalence. -/
@[simp]
theorem translationLatticeEquiv_symm (e : TranslationPreservingIso G H) :
    e.symm.translationLatticeEquiv = e.translationLatticeEquiv.symm := by
  apply LinearEquiv.ext
  intro t
  apply G.latticeTranslationEquiv.injective
  rw [e.symm.latticeTranslationEquiv_translationLatticeEquiv]
  rw [translationVectorEquiv_symm]
  apply e.translationVectorEquiv.injective
  rw [e.translationVectorEquiv.apply_symm_apply]
  simpa using e.latticeTranslationEquiv_translationLatticeEquiv
    (e.translationLatticeEquiv.symm t)

/-- Composition is consistent for the induced stored-lattice equivalence. -/
@[simp]
theorem translationLatticeEquiv_trans
    (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    (e.trans f).translationLatticeEquiv =
      e.translationLatticeEquiv.trans f.translationLatticeEquiv := by
  apply LinearEquiv.ext
  intro t
  apply K.latticeTranslationEquiv.injective
  simp

end TranslationPreservingIso

namespace PlaneGroup

/-- Two plane groups are equivalent when a translation-preserving abstract isomorphism exists. -/
def Equivalent (G H : PlaneGroup) : Prop :=
  Nonempty (TranslationPreservingIso G H)

namespace Equivalent

/-- Every plane group is equivalent to itself. -/
theorem refl (G : PlaneGroup) : Equivalent G G :=
  ⟨TranslationPreservingIso.refl G⟩

/-- Plane-group equivalence is symmetric. -/
theorem symm {G H : PlaneGroup} (h : Equivalent G H) : Equivalent H G := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/-- Plane-group equivalence is transitive. -/
theorem trans {G H K : PlaneGroup} (hGH : Equivalent G H) (hHK : Equivalent H K) :
    Equivalent G K := by
  rcases hGH with ⟨e⟩
  rcases hHK with ⟨f⟩
  exact ⟨e.trans f⟩

end Equivalent

/-- Translation-preserving equivalence is an equivalence relation on plane groups. -/
theorem equivalent_equivalence : Equivalence Equivalent :=
  by
    constructor
    · intro G
      exact Equivalent.refl G
    · intro G H h
      exact Equivalent.symm h
    · intro G H K hGH hHK
      exact Equivalent.trans hGH hHK

/-- Plane groups carry the setoid of translation-preserving abstract equivalence. -/
instance equivalentSetoid : Setoid PlaneGroup where
  r := Equivalent
  iseqv := equivalent_equivalence

/-- The point group is canonically the motion group modulo its translation kernel. -/
def pointQuotientEquiv (G : PlaneGroup) :
    G.carrier ⧸ translationSubgroup G.carrier ≃* pointGroup G.carrier :=
  QuotientGroup.quotientKerEquivRange (restrictedLinearPart G.carrier)

/-- The point-quotient equivalence sends a quotient representative to its point projection. -/
@[simp]
theorem pointQuotientEquiv_mk (G : PlaneGroup) (g : G.carrier) :
    G.pointQuotientEquiv (QuotientGroup.mk g) = pointProjection G.carrier g :=
  rfl

end PlaneGroup

namespace TranslationPreservingIso

variable {G H K : PlaneGroup}

/-- The equivalence induced on quotients by the two translation subgroups. -/
def quotientEquiv (e : TranslationPreservingIso G H) :
    G.carrier ⧸ translationSubgroup G.carrier ≃*
      H.carrier ⧸ translationSubgroup H.carrier :=
  QuotientGroup.congr (translationSubgroup G.carrier) (translationSubgroup H.carrier)
    e.toMulEquiv e.map_translationSubgroup

/-- The quotient equivalence maps the class of `g` to the class of its image. -/
@[simp]
theorem quotientEquiv_mk (e : TranslationPreservingIso G H) (g : G.carrier) :
    e.quotientEquiv (QuotientGroup.mk g) = QuotientGroup.mk (e.toMulEquiv g) :=
  rfl

/-- The canonical point-group equivalence induced by a translation-preserving isomorphism. -/
def pointGroupEquiv (e : TranslationPreservingIso G H) :
    pointGroup G.carrier ≃* pointGroup H.carrier :=
  G.pointQuotientEquiv.symm |>.trans <|
    e.quotientEquiv.trans H.pointQuotientEquiv

/-- The induced point-group equivalence commutes with the canonical point projections. -/
@[simp]
theorem pointGroupEquiv_pointProjection (e : TranslationPreservingIso G H)
    (g : G.carrier) :
    e.pointGroupEquiv (pointProjection G.carrier g) =
      pointProjection H.carrier (e.toMulEquiv g) := by
  change H.pointQuotientEquiv
      (e.quotientEquiv (G.pointQuotientEquiv.symm (pointProjection G.carrier g))) =
    pointProjection H.carrier (e.toMulEquiv g)
  rw [show pointProjection G.carrier g =
    G.pointQuotientEquiv (QuotientGroup.mk g) from rfl]
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The point-projection square commutes as an equality of bundled homomorphisms. -/
theorem pointProjection_commutes (e : TranslationPreservingIso G H) :
    e.pointGroupEquiv.toMonoidHom.comp (pointProjection G.carrier) =
      (pointProjection H.carrier).comp e.toMulEquiv.toMonoidHom := by
  apply MonoidHom.ext
  intro g
  exact e.pointGroupEquiv_pointProjection g

/-- The quotient equivalence of an identity isomorphism is the identity. -/
@[simp]
theorem quotientEquiv_refl :
    (refl G).quotientEquiv =
      MulEquiv.refl (G.carrier ⧸ translationSubgroup G.carrier) := by
  exact QuotientGroup.congr_refl (translationSubgroup G.carrier)

/-- The quotient construction commutes with taking inverses. -/
@[simp]
theorem quotientEquiv_symm (e : TranslationPreservingIso G H) :
    e.symm.quotientEquiv = e.quotientEquiv.symm := by
  exact (QuotientGroup.congr_symm
    (translationSubgroup G.carrier) (translationSubgroup H.carrier)
    e.toMulEquiv e.map_translationSubgroup).symm

/-- The quotient construction commutes with composition. -/
@[simp]
theorem quotientEquiv_trans
    (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    (e.trans f).quotientEquiv = e.quotientEquiv.trans f.quotientEquiv := by
  apply MulEquiv.ext
  rintro ⟨g⟩
  rfl

/-- The identity plane-group isomorphism induces the identity point-group isomorphism. -/
@[simp]
theorem pointGroupEquiv_refl :
    (refl G).pointGroupEquiv = MulEquiv.refl (pointGroup G.carrier) := by
  apply MulEquiv.ext
  intro h
  obtain ⟨g, rfl⟩ := pointProjection_surjective G.carrier h
  simp [refl]

/-- The point-group construction commutes with taking inverses. -/
@[simp]
theorem pointGroupEquiv_symm (e : TranslationPreservingIso G H) :
    e.symm.pointGroupEquiv = e.pointGroupEquiv.symm := by
  apply MulEquiv.ext
  intro h
  obtain ⟨g, rfl⟩ := pointProjection_surjective H.carrier h
  apply e.pointGroupEquiv.injective
  simp [symm]

/-- The inverse point-group equivalence sends a projected element to the projected inverse image. -/
@[simp]
theorem pointGroupEquiv_symm_pointProjection (e : TranslationPreservingIso G H)
    (g : H.carrier) :
    e.pointGroupEquiv.symm (pointProjection H.carrier g) =
      pointProjection G.carrier (e.toMulEquiv.symm g) := by
  rw [← e.pointGroupEquiv_symm]
  exact e.symm.pointGroupEquiv_pointProjection g

/-- The point-group construction commutes with composition. -/
@[simp]
theorem pointGroupEquiv_trans
    (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    (e.trans f).pointGroupEquiv = e.pointGroupEquiv.trans f.pointGroupEquiv := by
  apply MulEquiv.ext
  intro h
  obtain ⟨g, rfl⟩ := pointProjection_surjective G.carrier h
  simp [trans]

/-- Equivalent plane groups have point groups of equal cardinality. -/
theorem pointGroup_natCard_eq (e : TranslationPreservingIso G H) :
    Nat.card (pointGroup G.carrier) = Nat.card (pointGroup H.carrier) :=
  Nat.card_congr e.pointGroupEquiv.toEquiv

/-- Finiteness of the source point group transports along a translation-preserving isomorphism. -/
theorem pointGroup_finite_transport (e : TranslationPreservingIso G H) :
    Finite (pointGroup H.carrier) :=
  Finite.of_equiv (pointGroup G.carrier) e.pointGroupEquiv.toEquiv

end TranslationPreservingIso

namespace PlaneGroup

/-- Reframing a plane group's chosen lattice basis gives a translation-preserving identity map. -/
def reframeIso (G : PlaneGroup)
    (basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (hbasis : LinearIndependent ℝ (fun i => (basis i : Plane))) :
    TranslationPreservingIso G (G.reframe basis hbasis) where
  toMulEquiv := MulEquiv.refl G.carrier
  map_translationSubgroup := Subgroup.map_id _

/-- Changing only the chosen lattice frame does not change the plane-group equivalence class. -/
theorem reframe_equivalent (G : PlaneGroup)
    (basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (hbasis : LinearIndependent ℝ (fun i => (basis i : Plane))) :
    G.Equivalent (G.reframe basis hbasis) :=
  ⟨G.reframeIso basis hbasis⟩

end PlaneGroup

end


end WallpaperGroups
