import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option linter.style.header false

/-!
# M0 rank-two-lattice prototype

This file tests a thin wrapper around mathlib's `Submodule` and `Module.Basis` APIs.  It is M0
evidence rather than the stable M2 definition.
-/

set_option autoImplicit false

namespace WallpaperGroups.Prototype

noncomputable section

/--
The M0 lattice candidate: a `ℤ`-submodule with a chosen two-element integer basis whose vectors
remain linearly independent over `ℝ`.
-/
structure RankTwoLatticeCandidate (E : Type*) [AddCommGroup E] [Module ℝ E] where
  carrier : Submodule ℤ E
  basis : Module.Basis (Fin 2) ℤ carrier
  basis_real_linearIndependent :
    LinearIndependent ℝ (fun i => (basis i : E))

namespace RankTwoLatticeCandidate

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Unique integer coordinates in the chosen lattice basis. -/
def coordinates (L : RankTwoLatticeCandidate E) : L.carrier ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  L.basis.equivFun

/-- Rebuild a lattice element from a pair of integer coordinates. -/
def ofCoordinates (L : RankTwoLatticeCandidate E) : (Fin 2 → ℤ) ≃ₗ[ℤ] L.carrier :=
  L.coordinates.symm

@[simp]
theorem coordinates_ofCoordinates (L : RankTwoLatticeCandidate E) (z : Fin 2 → ℤ) :
    L.coordinates (L.ofCoordinates z) = z :=
  L.coordinates.apply_symm_apply z

@[simp]
theorem ofCoordinates_coordinates (L : RankTwoLatticeCandidate E) (x : L.carrier) :
    L.ofCoordinates (L.coordinates x) = x :=
  L.coordinates.symm_apply_apply x

@[simp]
theorem coordinates_basis (L : RankTwoLatticeCandidate E) (i : Fin 2) :
    L.coordinates (L.basis i) = Pi.single i 1 := by
  classical
  funext j
  simp [coordinates, Pi.single_apply, eq_comm]

/-- Integral matrix of a lattice automorphism in the chosen basis. -/
def automorphismMatrix (L : RankTwoLatticeCandidate E)
    (f : L.carrier ≃ₗ[ℤ] L.carrier) : Matrix (Fin 2) (Fin 2) ℤ :=
  LinearMap.toMatrix L.basis L.basis f.toLinearMap

/-- The same lattice automorphism as an element of `GL₂(ℤ)`. -/
def automorphismGL (L : RankTwoLatticeCandidate E)
    (f : L.carrier ≃ₗ[ℤ] L.carrier) : Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  (Matrix.GeneralLinearGroup.toLin' L.basis).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv f)

end RankTwoLatticeCandidate

/-- The coordinate plane used by the standard-lattice experiment. -/
abbrev PrototypePlane := Fin 2 → ℝ

/-- The standard real coordinate basis of `ℝ²`. -/
def standardRealBasis : Module.Basis (Fin 2) ℝ PrototypePlane :=
  Pi.basisFun ℝ (Fin 2)

/-- The standard copy of `ℤ²` inside `ℝ²`. -/
def standardLatticeCarrier : Submodule ℤ PrototypePlane :=
  Submodule.span ℤ (Set.range standardRealBasis)

/-- The two standard integer basis vectors, bundled as a basis of the standard lattice. -/
def standardIntegerBasis : Module.Basis (Fin 2) ℤ standardLatticeCarrier :=
  standardRealBasis.restrictScalars ℤ

/-- The standard `ℤ²` lattice as the candidate rank-two-lattice representation. -/
def standardRankTwoLattice : RankTwoLatticeCandidate PrototypePlane where
  carrier := standardLatticeCarrier
  basis := standardIntegerBasis
  basis_real_linearIndependent := by
    change LinearIndependent ℝ
      (fun i => ((standardIntegerBasis i : standardLatticeCarrier) : PrototypePlane))
    have h : (fun i => ((standardIntegerBasis i : standardLatticeCarrier) : PrototypePlane)) =
        standardRealBasis := by
      funext i
      exact Module.Basis.restrictScalars_apply ℤ standardRealBasis i
    rw [h]
    exact standardRealBasis.linearIndependent

noncomputable instance standardLatticeCarrierDiscrete :
    DiscreteTopology standardLatticeCarrier := by
  unfold standardLatticeCarrier standardRealBasis
  infer_instance

noncomputable instance standardLatticeCarrierIsZLattice :
    IsZLattice ℝ standardLatticeCarrier := by
  unfold standardLatticeCarrier standardRealBasis
  infer_instance

example (z : Fin 2 → ℤ) :
    standardRankTwoLattice.coordinates (standardRankTwoLattice.ofCoordinates z) = z := by
  simp

example (x : standardRankTwoLattice.carrier) :
    standardRankTwoLattice.ofCoordinates (standardRankTwoLattice.coordinates x) = x := by
  simp

example :
    LinearIndependent ℝ (fun i => (standardRankTwoLattice.basis i : PrototypePlane)) :=
  standardRankTwoLattice.basis_real_linearIndependent

end

end WallpaperGroups.Prototype
