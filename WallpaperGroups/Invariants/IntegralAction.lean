import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import WallpaperGroups.Basic.PlaneGroup

set_option linter.style.header false

/-!
# Faithful integral point-group action

The point group of a plane group preserves its full translation lattice.  This module transports
the M1 action on translation vectors to the stored lattice carrier, promotes it canonically to a
`ℤ`-linear action, and records the resulting faithful matrix representation in `GL₂(ℤ)`.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

namespace PlaneGroup

/-- The point action transported from translation vectors to the stored lattice carrier. -/
def latticeActionAddEquiv (G : PlaneGroup) (h : pointGroup G.carrier) :
    AddAut G.translationLattice.carrier :=
  G.latticeTranslationEquiv.trans
    ((pointAction G.carrier h).trans G.latticeTranslationEquiv.symm)

/-- The transported additive action has the expected underlying action on plane vectors. -/
@[simp]
theorem latticeActionAddEquiv_coe (G : PlaneGroup) (h : pointGroup G.carrier)
    (t : G.translationLattice.carrier) :
    (G.latticeActionAddEquiv h t : Plane) =
      (h : Plane ≃ₗᵢ[ℝ] Plane) (t : Plane) :=
  rfl

/-- The point-group action on the translation lattice, promoted canonically to a `ℤ`-linear map. -/
def latticeAction (G : PlaneGroup) (h : pointGroup G.carrier) :
    G.translationLattice.carrier ≃ₗ[ℤ] G.translationLattice.carrier :=
  (G.latticeActionAddEquiv h).toIntLinearEquiv

/-- The integer-linear lattice action agrees with the ambient linear isometry. -/
@[simp]
theorem latticeAction_coe (G : PlaneGroup) (h : pointGroup G.carrier)
    (t : G.translationLattice.carrier) :
    (G.latticeAction h t : Plane) =
      (h : Plane ≃ₗᵢ[ℝ] Plane) (t : Plane) :=
  rfl

/-- The identity point-group element acts trivially on the translation lattice. -/
@[simp]
theorem latticeAction_one (G : PlaneGroup) :
    G.latticeAction 1 = LinearEquiv.refl ℤ G.translationLattice.carrier := by
  apply LinearEquiv.ext
  intro t
  apply Subtype.ext
  rfl

/-- Point-group multiplication becomes composition of lattice automorphisms in the same order. -/
theorem latticeAction_mul (G : PlaneGroup) (h k : pointGroup G.carrier) :
    G.latticeAction (h * k) = G.latticeAction h * G.latticeAction k := by
  apply LinearEquiv.ext
  intro t
  apply Subtype.ext
  rfl

/-- Inversion in the point group becomes inversion of the lattice automorphism. -/
@[simp]
theorem latticeAction_inv (G : PlaneGroup) (h : pointGroup G.carrier) :
    G.latticeAction h⁻¹ = (G.latticeAction h)⁻¹ := by
  apply LinearEquiv.ext
  intro t
  apply Subtype.ext
  rfl

/-- The integral lattice action bundled as a group homomorphism. -/
def latticeActionHom (G : PlaneGroup) :
    pointGroup G.carrier →*
      (G.translationLattice.carrier ≃ₗ[ℤ] G.translationLattice.carrier) where
  toFun := G.latticeAction
  map_one' := G.latticeAction_one
  map_mul' := G.latticeAction_mul

/-- Evaluating the bundled action homomorphism recovers the explicit lattice action. -/
@[simp]
theorem latticeActionHom_apply (G : PlaneGroup) (h : pointGroup G.carrier) :
    G.latticeActionHom h = G.latticeAction h :=
  rfl

/-- The point group acts faithfully on the full rank-two translation lattice. -/
theorem latticeActionHom_injective (G : PlaneGroup) :
    Function.Injective G.latticeActionHom := by
  intro h k hhk
  apply Subtype.ext
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply G.realBasis.ext
  intro i
  rw [G.translationLattice.realBasis_apply]
  have hi := congrArg
    (fun f : G.translationLattice.carrier ≃ₗ[ℤ]
      G.translationLattice.carrier => f (G.translationLattice.basis i)) hhk
  calc
    (h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv
        (G.translationLattice.basis i : Plane) =
        (h : Plane ≃ₗᵢ[ℝ] Plane)
          (G.translationLattice.basis i : Plane) := rfl
    _ = (k : Plane ≃ₗᵢ[ℝ] Plane)
          (G.translationLattice.basis i : Plane) := by
      simpa only [latticeActionHom_apply, latticeAction_coe] using
        congrArg Subtype.val hi
    _ = (k : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv
        (G.translationLattice.basis i : Plane) := rfl

/-- The integer matrix of a point-group element in the chosen translation-lattice basis. -/
def latticeActionMatrix (G : PlaneGroup) (h : pointGroup G.carrier) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  G.translationLattice.equivMatrix G.translationLattice (G.latticeAction h)

/-- The identity point-group element has identity integral action matrix. -/
@[simp]
theorem latticeActionMatrix_one (G : PlaneGroup) :
    G.latticeActionMatrix 1 = 1 := by
  rw [latticeActionMatrix, latticeAction_one]
  exact G.translationLattice.equivMatrix_refl

/-- Integral action matrices preserve point-group multiplication. -/
theorem latticeActionMatrix_mul (G : PlaneGroup) (h k : pointGroup G.carrier) :
    G.latticeActionMatrix (h * k) =
      G.latticeActionMatrix h * G.latticeActionMatrix k := by
  unfold latticeActionMatrix RankTwoLattice.equivMatrix
  rw [latticeAction_mul]
  exact LinearMap.toMatrix_mul G.translationLattice.basis
    (G.latticeAction h).toLinearMap (G.latticeAction k).toLinearMap

/-- The matrix-valued integral action is injective. -/
theorem latticeActionMatrix_injective (G : PlaneGroup) :
    Function.Injective G.latticeActionMatrix := by
  intro h k hhk
  apply G.latticeActionHom_injective
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix G.translationLattice.basis
    G.translationLattice.basis).injective
  exact hhk

/-- The faithful integral point-group representation in `GL₂(ℤ)`. -/
def integralRepresentation (G : PlaneGroup) :
    pointGroup G.carrier →* Matrix.GeneralLinearGroup (Fin 2) ℤ where
  toFun h :=
    G.translationLattice.equivGL G.translationLattice (G.latticeAction h)
  map_one' := by
    rw [latticeAction_one]
    exact G.translationLattice.equivGL_refl
  map_mul' h k := by
    apply Units.ext
    exact G.latticeActionMatrix_mul h k

/-- Evaluating the integral representation gives the bundled matrix of the lattice action. -/
@[simp]
theorem integralRepresentation_apply (G : PlaneGroup) (h : pointGroup G.carrier) :
    G.integralRepresentation h =
      G.translationLattice.equivGL G.translationLattice (G.latticeAction h) :=
  rfl

/-- Coercing the integral representation to a matrix recovers `latticeActionMatrix`. -/
@[simp]
theorem integralRepresentation_coe (G : PlaneGroup) (h : pointGroup G.carrier) :
    (G.integralRepresentation h : Matrix (Fin 2) (Fin 2) ℤ) =
      G.latticeActionMatrix h :=
  rfl

/-- The integral representation preserves multiplication. -/
theorem integralRepresentation_mul (G : PlaneGroup) (h k : pointGroup G.carrier) :
    G.integralRepresentation (h * k) =
      G.integralRepresentation h * G.integralRepresentation k :=
  map_mul G.integralRepresentation h k

/-- The integral representation preserves inversion. -/
@[simp]
theorem integralRepresentation_inv (G : PlaneGroup) (h : pointGroup G.carrier) :
    G.integralRepresentation h⁻¹ = (G.integralRepresentation h)⁻¹ :=
  map_inv G.integralRepresentation h

/-- The `GL₂(ℤ)` representation of the point group is faithful. -/
theorem integralRepresentation_injective (G : PlaneGroup) :
    Function.Injective G.integralRepresentation := by
  intro h k hhk
  apply G.latticeActionHom_injective
  apply G.translationLattice.equivGL_injective G.translationLattice
  exact hhk

end PlaneGroup

end

end WallpaperGroups
