import WallpaperGroups.Basic.Equivalence
import WallpaperGroups.Invariants.IntegralAction

set_option linter.style.header false

/-!
# Action transport under translation-preserving equivalence

This module proves that the lattice and point-group maps induced by an abstract
translation-preserving group isomorphism intertwine the point actions.  It then extends the
lattice map to an ordinary real-linear equivalence of the plane and derives the corresponding
integer matrix conjugacy.  The real-linear map is not asserted to be an isometry.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

namespace TranslationPreservingIso

variable {G H K : PlaneGroup}

/--
The induced translation-vector equivalence intertwines the two coordinate-free point actions.
This is the algebraic consequence of applying the abstract group isomorphism to conjugation of a
pure translation by a lift of the point-group element.
-/
theorem translationVector_pointAction (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) (t : translationVectors G.carrier) :
    e.translationVectorEquiv (pointAction G.carrier h t) =
      pointAction H.carrier (e.pointGroupEquiv h) (e.translationVectorEquiv t) := by
  obtain ⟨g, rfl⟩ := pointProjection_surjective G.carrier h
  have hmapped :
      e.toMulEquiv g *
          translationElement H.carrier (e.translationVectorEquiv t) *
          (e.toMulEquiv g)⁻¹ =
        translationElement H.carrier
          (e.translationVectorEquiv
            (pointAction G.carrier (pointProjection G.carrier g) t)) := by
    calc
      e.toMulEquiv g *
            translationElement H.carrier (e.translationVectorEquiv t) *
            (e.toMulEquiv g)⁻¹ =
          e.toMulEquiv (g * translationElement G.carrier t * g⁻¹) := by
        rw [map_mul, map_mul, map_inv, e.map_translationElement]
      _ = e.toMulEquiv
          (translationElement G.carrier
            (pointAction G.carrier (pointProjection G.carrier g) t)) := by
        rw [conjugate_translationElement]
      _ = translationElement H.carrier
          (e.translationVectorEquiv
            (pointAction G.carrier (pointProjection G.carrier g) t)) :=
        e.map_translationElement _
  have htarget := conjugate_translationElement H.carrier (e.toMulEquiv g)
    (e.translationVectorEquiv t)
  have helements :
      translationElement H.carrier
          (e.translationVectorEquiv
            (pointAction G.carrier (pointProjection G.carrier g) t)) =
        translationElement H.carrier
          (pointAction H.carrier (pointProjection H.carrier (e.toMulEquiv g))
            (e.translationVectorEquiv t)) :=
    hmapped.symm.trans htarget
  have hvectors :
      e.translationVectorEquiv
          (pointAction G.carrier (pointProjection G.carrier g) t) =
        pointAction H.carrier (pointProjection H.carrier (e.toMulEquiv g))
          (e.translationVectorEquiv t) := by
    apply Subtype.ext
    apply translation_injective
    exact congrArg (fun x : H.carrier => (x : EuclideanMotion Plane)) helements
  simpa only [e.pointGroupEquiv_pointProjection] using hvectors

/-- The carrier adapter commutes with the integral point action. -/
@[simp]
theorem latticeTranslationEquiv_latticeAction (G : PlaneGroup)
    (h : pointGroup G.carrier) (t : G.translationLattice.carrier) :
    G.latticeTranslationEquiv (G.latticeAction h t) =
      pointAction G.carrier h (G.latticeTranslationEquiv t) :=
  rfl

/-- The induced integer-linear lattice equivalence intertwines the two lattice actions. -/
theorem translationLattice_pointAction (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) (t : G.translationLattice.carrier) :
    e.translationLatticeEquiv (G.latticeAction h t) =
      H.latticeAction (e.pointGroupEquiv h) (e.translationLatticeEquiv t) := by
  apply H.latticeTranslationEquiv.injective
  rw [e.latticeTranslationEquiv_translationLatticeEquiv]
  rw [latticeTranslationEquiv_latticeAction H]
  rw [latticeTranslationEquiv_latticeAction G]
  rw [e.translationVector_pointAction]
  rw [e.latticeTranslationEquiv_translationLatticeEquiv]

/-- The lattice-action intertwining relation as an equality of integer-linear maps. -/
theorem latticeAction_intertwining (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) :
    e.translationLatticeEquiv.toLinearMap.comp (G.latticeAction h).toLinearMap =
      (H.latticeAction (e.pointGroupEquiv h)).toLinearMap.comp
        e.translationLatticeEquiv.toLinearMap := by
  apply LinearMap.ext
  intro t
  exact e.translationLattice_pointAction h t

/-- The same intertwining relation bundled as a commuting square of linear equivalences. -/
theorem latticeAction_conjugacy (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) :
    (G.latticeAction h).trans e.translationLatticeEquiv =
      e.translationLatticeEquiv.trans (H.latticeAction (e.pointGroupEquiv h)) := by
  apply LinearEquiv.ext
  intro t
  exact e.translationLattice_pointAction h t

/--
The real-linear plane equivalence extending the induced lattice equivalence.  It is constructed
from the integral equivalence matrix and the real bases determined by the two chosen lattice
frames.  It need not preserve the Euclidean norm or inner product.
-/
def realLinearEquiv (e : TranslationPreservingIso G H) : Plane ≃ₗ[ℝ] Plane :=
  G.translationLattice.extendEquiv H.translationLattice e.translationLatticeEquiv

/-- The real-linear extension agrees with the induced map on every lattice element. -/
@[simp]
theorem realLinearEquiv_agrees (e : TranslationPreservingIso G H)
    (t : G.translationLattice.carrier) :
    e.realLinearEquiv (t : Plane) = (e.translationLatticeEquiv t : Plane) :=
  G.translationLattice.extendEquiv_agrees H.translationLattice
    e.translationLatticeEquiv t

/-- Taking an inverse group isomorphism gives the inverse real-linear extension. -/
@[simp]
theorem realLinearEquiv_symm (e : TranslationPreservingIso G H) :
    e.symm.realLinearEquiv = e.realLinearEquiv.symm := by
  rw [realLinearEquiv, e.translationLatticeEquiv_symm]
  exact G.translationLattice.extendEquiv_symm H.translationLattice
    e.translationLatticeEquiv

/-- The identity translation-preserving isomorphism extends to the identity of the plane. -/
@[simp]
theorem realLinearEquiv_refl :
    (refl G).realLinearEquiv = LinearEquiv.refl ℝ Plane := by
  rw [realLinearEquiv, translationLatticeEquiv_refl]
  exact G.translationLattice.extendEquiv_refl

/-- Real-linear extension preserves composition of translation-preserving isomorphisms. -/
theorem realLinearEquiv_trans
    (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    (e.trans f).realLinearEquiv = e.realLinearEquiv.trans f.realLinearEquiv := by
  rw [realLinearEquiv, translationLatticeEquiv_trans]
  exact G.translationLattice.extendEquiv_trans H.translationLattice K.translationLattice
    e.translationLatticeEquiv f.translationLatticeEquiv

/--
The real-linear extension intertwines the ambient linear actions on the entire plane.  This is
the formal version of the paper's relation `φ' = λ φ λ⁻¹`; `λ` is general linear, not orthogonal.
-/
theorem realLinearEquiv_pointAction (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) (x : Plane) :
    e.realLinearEquiv ((h : Plane ≃ₗᵢ[ℝ] Plane) x) =
      (e.pointGroupEquiv h : Plane ≃ₗᵢ[ℝ] Plane) (e.realLinearEquiv x) := by
  let lhs : Plane →ₗ[ℝ] Plane :=
    e.realLinearEquiv.toLinearMap.comp
      (h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap
  let rhs : Plane →ₗ[ℝ] Plane :=
    (e.pointGroupEquiv h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap.comp
      e.realLinearEquiv.toLinearMap
  have hmaps : lhs = rhs := by
    apply G.realBasis.ext
    intro i
    rw [G.translationLattice.realBasis_apply]
    change e.realLinearEquiv
        ((h : Plane ≃ₗᵢ[ℝ] Plane) (G.translationLattice.basis i : Plane)) =
      (e.pointGroupEquiv h : Plane ≃ₗᵢ[ℝ] Plane)
        (e.realLinearEquiv (G.translationLattice.basis i : Plane))
    calc
      e.realLinearEquiv
          ((h : Plane ≃ₗᵢ[ℝ] Plane) (G.translationLattice.basis i : Plane)) =
        e.realLinearEquiv
          (G.latticeAction h (G.translationLattice.basis i) : Plane) := by
            rw [G.latticeAction_coe]
      _ = (e.translationLatticeEquiv
          (G.latticeAction h (G.translationLattice.basis i)) : Plane) :=
        e.realLinearEquiv_agrees _
      _ = (H.latticeAction (e.pointGroupEquiv h)
          (e.translationLatticeEquiv (G.translationLattice.basis i)) : Plane) := by
        exact congrArg Subtype.val
          (e.translationLattice_pointAction h (G.translationLattice.basis i))
      _ = (e.pointGroupEquiv h : Plane ≃ₗᵢ[ℝ] Plane)
          (e.translationLatticeEquiv (G.translationLattice.basis i) : Plane) := by
        rw [H.latticeAction_coe]
      _ = (e.pointGroupEquiv h : Plane ≃ₗᵢ[ℝ] Plane)
          (e.realLinearEquiv (G.translationLattice.basis i : Plane)) := by
        rw [e.realLinearEquiv_agrees]
  exact LinearMap.congr_fun hmaps x

/-- The ambient action intertwining relation as an equality of real-linear maps. -/
theorem ambientAction_intertwining (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) :
    e.realLinearEquiv.toLinearMap.comp
        (h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap =
      (e.pointGroupEquiv h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap.comp
        e.realLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact e.realLinearEquiv_pointAction h x

/-- The induced lattice equivalence gives the expected integral matrix commuting relation. -/
theorem integralMatrix_intertwining (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) :
    G.translationLattice.equivMatrix H.translationLattice e.translationLatticeEquiv *
        G.latticeActionMatrix h =
      H.latticeActionMatrix (e.pointGroupEquiv h) *
        G.translationLattice.equivMatrix H.translationLattice e.translationLatticeEquiv := by
  exact G.translationLattice.matrix_intertwining H.translationLattice
    e.translationLatticeEquiv (G.latticeAction h)
      (H.latticeAction (e.pointGroupEquiv h)) (e.latticeAction_intertwining h)

/--
A translation-preserving group isomorphism conjugates the selected-basis integral action
matrices.  With mathlib's column-vector convention this is `A' = P * A * P⁻¹`.
-/
theorem integralMatrix_conjugacy (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) :
    H.latticeActionMatrix (e.pointGroupEquiv h) =
      G.translationLattice.equivMatrix H.translationLattice e.translationLatticeEquiv *
        G.latticeActionMatrix h *
          H.translationLattice.equivMatrix G.translationLattice
            e.translationLatticeEquiv.symm := by
  exact G.translationLattice.matrix_conjugacy H.translationLattice
    e.translationLatticeEquiv (G.latticeAction h)
      (H.latticeAction (e.pointGroupEquiv h)) (e.latticeAction_intertwining h)

/-- The same conjugacy packaged inside `GL₂(ℤ)`. -/
theorem integralRepresentation_conjugacy (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) :
    H.integralRepresentation (e.pointGroupEquiv h) =
      G.translationLattice.equivGL H.translationLattice e.translationLatticeEquiv *
        G.integralRepresentation h *
          (G.translationLattice.equivGL H.translationLattice
            e.translationLatticeEquiv)⁻¹ := by
  apply Units.ext
  exact e.integralMatrix_conjugacy h

end TranslationPreservingIso

end


end WallpaperGroups
