import WallpaperGroups.Models.Common
import WallpaperGroups.Restriction.LatticeNormalForms
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option linter.style.header false

/-!
# Standard reflection-free rotation models

This module constructs the square and triangular lattices in explicit complex coordinates and
uses the transparent symmorphic normal form to define the five reflection-free wallpaper models.
Their point groups have orders `1`, `2`, `3`, `4`, and `6`, and every point element preserves
orientation.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion
open scoped RealInnerProductSpace

noncomputable section

/-- Canonical coordinate isometry from the Euclidean plane to the complex plane. -/
def coordinateIsometry : Plane ≃ₗᵢ[ℝ] ℂ :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).equiv
    Complex.orthonormalBasisOneI (Equiv.refl (Fin 2))

@[simp]
lemma coordinateIsometry_basis_zero :
    coordinateIsometry (Plane.canonicalRealBasis 0) = 1 := by
  change ((EuclideanSpace.basisFun (Fin 2) ℝ).equiv
    Complex.orthonormalBasisOneI (Equiv.refl (Fin 2)))
      ((EuclideanSpace.basisFun (Fin 2) ℝ) 0) = 1
  rw [OrthonormalBasis.equiv_apply_basis]
  change Complex.basisOneI 0 = 1
  simp [Complex.coe_basisOneI]

@[simp]
lemma coordinateIsometry_basis_one :
    coordinateIsometry (Plane.canonicalRealBasis 1) = Complex.I := by
  change ((EuclideanSpace.basisFun (Fin 2) ℝ).equiv
    Complex.orthonormalBasisOneI (Equiv.refl (Fin 2)))
      ((EuclideanSpace.basisFun (Fin 2) ℝ) 1) = Complex.I
  rw [OrthonormalBasis.equiv_apply_basis]
  change Complex.basisOneI 1 = Complex.I
  simp [Complex.coe_basisOneI]

/-- The primitive positive sixth root of unity used for the triangular lattice. -/
def hexRoot : Circle where
  val := (1 / 2 : ℝ) + (Real.sqrt 3 / 2 : ℝ) * Complex.I
  property := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.norm_def]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, Complex.add_im, zero_add,
      mul_one]
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [show (1 / 2 : ℝ) * (1 / 2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 by
      nlinarith]
    simp

lemma hexRoot_poly : (hexRoot : ℂ) ^ 2 - hexRoot + 1 = 0 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [hexRoot, pow_two, Complex.mul_re, Complex.mul_im]
    nlinarith
  · simp [hexRoot, pow_two, Complex.mul_re, Complex.mul_im]
    ring

lemma hexRoot_sq_ne_one : hexRoot ^ 2 ≠ 1 := by
  intro h
  have hc := congrArg (fun z : Circle => (z : ℂ)) h
  have hp := hexRoot_poly
  have hc' : (hexRoot : ℂ) ^ 2 = 1 := by simpa using hc
  rw [hc'] at hp
  have him := congrArg Complex.im hp
  simp [hexRoot] at him

lemma hexRoot_cube_ne_one : hexRoot ^ 3 ≠ 1 := by
  intro h
  have hc := congrArg (fun z : Circle => (z : ℂ)) h
  have hp := hexRoot_poly
  have hpoly : (hexRoot : ℂ) ^ 2 = (hexRoot : ℂ) - 1 := by
    linear_combination hexRoot_poly
  have hcube : (hexRoot : ℂ) ^ 3 = -1 := by
    rw [show (hexRoot : ℂ) ^ 3 = (hexRoot : ℂ) * (hexRoot : ℂ) ^ 2 by ring,
      hpoly]
    linear_combination hexRoot_poly
  have hc' : (hexRoot : ℂ) ^ 3 = 1 := by simpa using hc
  rw [hcube] at hc'
  norm_num at hc'

lemma hexRoot_pow_six : hexRoot ^ 6 = 1 := by
  apply Circle.ext
  have hcube : (hexRoot : ℂ) ^ 3 = -1 := by
    have hpoly : (hexRoot : ℂ) ^ 2 = (hexRoot : ℂ) - 1 := by
      linear_combination hexRoot_poly
    rw [show (hexRoot : ℂ) ^ 3 = (hexRoot : ℂ) * (hexRoot : ℂ) ^ 2 by ring,
      hpoly]
    linear_combination hexRoot_poly
  change (hexRoot : ℂ) ^ 6 = 1
  rw [show (hexRoot : ℂ) ^ 6 = ((hexRoot : ℂ) ^ 3) ^ 2 by ring, hcube]
  norm_num

lemma hexRoot_order : orderOf hexRoot = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hexRoot_pow_six
  intro p hp hd
  have hp23 : p ∣ 2 * 3 := by simpa using hd
  rcases (hp.dvd_mul).mp hp23 with hp2 | hp3
  · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    subst p
    norm_num
    exact hexRoot_cube_ne_one
  · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
    subst p
    norm_num
    exact hexRoot_sq_ne_one

/-- The fourth root `i`, as an element of the unit circle. -/
def squareRoot : Circle where
  val := Complex.I
  property := by
    simp [Submonoid.unitSphere]

lemma squareRoot_sq : squareRoot ^ 2 = -1 := by
  apply Circle.ext
  change Complex.I ^ 2 = (-1 : ℂ)
  rw [pow_two, Complex.I_mul_I]

lemma squareRoot_pow_four : squareRoot ^ 4 = 1 := by
  calc
    squareRoot ^ 4 = (squareRoot ^ 2) ^ 2 := by group
    _ = 1 := by rw [squareRoot_sq]; simp

lemma squareRoot_order : orderOf squareRoot = 4 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  refine ⟨squareRoot_pow_four, ?_⟩
  intro m hm hpos
  interval_cases m <;> norm_num at hpos hm ⊢
  · intro h
    have hc := congrArg (fun z : Circle => (z : ℂ)) h
    have him := congrArg Complex.im hc
    norm_num [squareRoot] at him
  · intro h
    rw [squareRoot_sq] at h
    have hc := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at hc
  · intro h
    have hs : squareRoot = 1 := by
      calc
        squareRoot = squareRoot ^ 4 * (squareRoot ^ 3)⁻¹ := by group
        _ = 1 := by rw [squareRoot_pow_four, h]; simp
    have hc := congrArg (fun z : Circle => (z : ℂ)) hs
    have him := congrArg Complex.im hc
    norm_num [squareRoot] at him

/-- Conjugate complex multiplication by `a` back to the coordinate plane. -/
def planeRotation (a : Circle) : Plane ≃ₗᵢ[ℝ] Plane :=
  (coordinateIsometry.trans (_root_.rotation a)).trans coordinateIsometry.symm

@[simp]
lemma coordinateIsometry_planeRotation (a : Circle) (x : Plane) :
    coordinateIsometry (planeRotation a x) = (a : ℂ) * coordinateIsometry x := by
  simp [planeRotation, _root_.rotation_apply]

@[simp]
lemma planeRotation_mul (a b : Circle) :
    planeRotation (a * b) = planeRotation a * planeRotation b := by
  apply LinearIsometryEquiv.ext
  intro x
  apply coordinateIsometry.injective
  simp [mul_assoc]

@[simp]
lemma planeRotation_one : planeRotation 1 = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  apply coordinateIsometry.injective
  simp

def planeRotationHom : Circle →* (Plane ≃ₗᵢ[ℝ] Plane) where
  toFun := planeRotation
  map_one' := planeRotation_one
  map_mul' := planeRotation_mul

lemma planeRotationHom_injective : Function.Injective planeRotationHom := by
  intro a b h
  have h0 := LinearIsometryEquiv.congr_fun h (coordinateIsometry.symm 1)
  have hc := congrArg coordinateIsometry h0
  apply Circle.ext
  simpa [planeRotationHom] using hc

lemma planeRotation_order (a : Circle) : orderOf (planeRotation a) = orderOf a :=
  orderOf_injective planeRotationHom planeRotationHom_injective a

/-- Conjugating complex multiplication back to the plane preserves determinant one. -/
lemma planeRotation_det (a : Circle) :
    LinearMap.det
      ((planeRotation a).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 := by
  change LinearMap.det
      (((coordinateIsometry.toLinearEquiv.trans
        (_root_.rotation a).toLinearEquiv).trans
          coordinateIsometry.symm.toLinearEquiv : Plane ≃ₗ[ℝ] Plane) :
            Plane →ₗ[ℝ] Plane) = 1
  have h := congrArg Units.val
    (LinearEquiv.det_conj (_root_.rotation a).toLinearEquiv
      coordinateIsometry.symm.toLinearEquiv)
  convert h using 1 <;> simp

/-- Real-linear change of coordinates taking `(1,i)` to `(1,ζ₆)`. -/
def hexShear : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := (z.re : ℂ) + (z.im : ℂ) * (hexRoot : ℂ)
  invFun z := ((z.re - z.im / Real.sqrt 3 : ℝ) : ℂ) +
    ((2 * z.im / Real.sqrt 3 : ℝ) : ℂ) * Complex.I
  map_add' z w := by
    apply Complex.ext <;>
      simp [hexRoot, Complex.mul_re, Complex.mul_im] <;> ring
  map_smul' r z := by
    apply Complex.ext <;>
      simp [hexRoot, Complex.mul_re, Complex.mul_im] <;> ring
  left_inv z := by
    have hs : Real.sqrt 3 ≠ 0 := by positivity
    apply Complex.ext
    · simp [hexRoot, Complex.mul_re, Complex.mul_im]
      field_simp [hs]
      ring
    · simp [hexRoot, Complex.mul_re, Complex.mul_im]
      field_simp [hs]
  right_inv z := by
    have hs : Real.sqrt 3 ≠ 0 := by positivity
    apply Complex.ext
    · simp [hexRoot, Complex.mul_re, Complex.mul_im]
      field_simp [hs]
      ring
    · simp [hexRoot, Complex.mul_re, Complex.mul_im]
      field_simp [hs]

@[simp]
lemma hexShear_one : hexShear 1 = 1 := by
  apply Complex.ext <;> simp [hexShear, hexRoot]

@[simp]
lemma hexShear_I : hexShear Complex.I = (hexRoot : ℂ) := by
  apply Complex.ext <;> simp [hexShear, hexRoot]

/-- Change of basis carrying the square coordinate frame to the triangular frame. -/
def hexPlaneEquiv : Plane ≃ₗ[ℝ] Plane :=
  (coordinateIsometry.toLinearEquiv.trans hexShear).trans
    coordinateIsometry.symm.toLinearEquiv

/-- The framed triangular lattice with complex-coordinate basis `(1,ζ₆)`. -/
def hexLattice : RankTwoLattice Plane :=
  RankTwoLattice.standardLattice.map hexPlaneEquiv

@[simp]
lemma standardLattice_basis_coe (i : Fin 2) :
    (RankTwoLattice.standardLattice.basis i : Plane) =
      Plane.canonicalRealBasis i := by
  exact Module.Basis.restrictScalars_apply ℤ Plane.canonicalRealBasis i

@[simp]
lemma coordinateIsometry_hexLattice_basis_zero :
    coordinateIsometry (hexLattice.basis 0 : Plane) = 1 := by
  rw [show (hexLattice.basis 0 : Plane) =
      hexPlaneEquiv (RankTwoLattice.standardLattice.basis 0 : Plane) by rfl]
  rw [standardLattice_basis_coe]
  unfold hexPlaneEquiv
  change coordinateIsometry
      (coordinateIsometry.symm
        (hexShear (coordinateIsometry (Plane.canonicalRealBasis 0)))) = 1
  rw [coordinateIsometry.apply_symm_apply, coordinateIsometry_basis_zero,
    hexShear_one]

@[simp]
lemma coordinateIsometry_hexLattice_basis_one :
    coordinateIsometry (hexLattice.basis 1 : Plane) = (hexRoot : ℂ) := by
  rw [show (hexLattice.basis 1 : Plane) =
      hexPlaneEquiv (RankTwoLattice.standardLattice.basis 1 : Plane) by rfl]
  rw [standardLattice_basis_coe]
  unfold hexPlaneEquiv
  change coordinateIsometry
      (coordinateIsometry.symm
        (hexShear (coordinateIsometry (Plane.canonicalRealBasis 1)))) = (hexRoot : ℂ)
  rw [coordinateIsometry.apply_symm_apply, coordinateIsometry_basis_one,
    hexShear_I]

@[simp]
lemma coordinateIsometry_squareLattice_basis_zero :
    coordinateIsometry (RankTwoLattice.standardLattice.basis 0 : Plane) = 1 := by
  simp only [standardLattice_basis_coe, Plane.canonicalRealBasis_apply]
  rw [← Plane.canonicalRealBasis_apply, coordinateIsometry_basis_zero]

@[simp]
lemma coordinateIsometry_squareLattice_basis_one :
    coordinateIsometry (RankTwoLattice.standardLattice.basis 1 : Plane) = Complex.I := by
  simp only [standardLattice_basis_coe, Plane.canonicalRealBasis_apply]
  rw [← Plane.canonicalRealBasis_apply, coordinateIsometry_basis_one]

/-- A linear map preserving the displayed integral basis preserves the whole lattice. -/
lemma map_mem_lattice_of_basis
    (L : RankTwoLattice Plane) (A : Plane →ₗ[ℝ] Plane)
    (hA : ∀ i, A (L.basis i : Plane) ∈ L.carrier)
    {x : Plane} (hx : x ∈ L.carrier) : A x ∈ L.carrier := by
  rw [L.carrier_eq_zspan_realBasis] at hx ⊢
  refine Submodule.span_induction (p := fun x _ => A x ∈
      Submodule.span ℤ (Set.range L.realBasis)) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, rfl⟩
    rw [L.realBasis_apply]
    rw [← L.carrier_eq_zspan_realBasis]
    exact hA i
  · rw [map_zero]
    exact Submodule.zero_mem (Submodule.span ℤ (Set.range L.realBasis))
  · intro x y hx hy hmx hmy
    simpa only [map_add] using
      (Submodule.add_mem (Submodule.span ℤ (Set.range L.realBasis)) hmx hmy)
  · intro a x hx hmx
    simpa only [map_zsmul] using
      (Submodule.smul_mem (Submodule.span ℤ (Set.range L.realBasis)) a hmx)

/-- Linear isometries that preserve a lattice in both directions. -/
def latticeStabilizer (L : RankTwoLattice Plane) :
    Subgroup (Plane ≃ₗᵢ[ℝ] Plane) where
  carrier := {A | ∀ x : Plane, x ∈ L.carrier ↔ A x ∈ L.carrier}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB x
    exact (hB x).trans (hA (B x))
  inv_mem' := by
    intro A hA x
    simpa using (hA (A⁻¹ x)).symm

/-- Basis preservation by an isometry and its inverse gives stabilizer membership. -/
lemma mem_latticeStabilizer_of_basis
    (L : RankTwoLattice Plane) (A : Plane ≃ₗᵢ[ℝ] Plane)
    (hA : ∀ i, A (L.basis i : Plane) ∈ L.carrier)
    (hAi : ∀ i, A⁻¹ (L.basis i : Plane) ∈ L.carrier) :
    A ∈ latticeStabilizer L := by
  intro x
  constructor
  · exact map_mem_lattice_of_basis L A.toLinearEquiv.toLinearMap hA
  · intro hx
    have hi := map_mem_lattice_of_basis L A.symm.toLinearEquiv.toLinearMap hAi hx
    simpa using hi

@[simp]
lemma planeRotation_inv (a : Circle) :
    (planeRotation a)⁻¹ = planeRotation a⁻¹ := by
  exact (map_inv planeRotationHom a).symm

lemma hexRoot_coe_inv : ((hexRoot⁻¹ : Circle) : ℂ) = 1 - (hexRoot : ℂ) := by
  change (hexRoot : ℂ)⁻¹ = 1 - (hexRoot : ℂ)
  apply inv_eq_of_mul_eq_one_right
  linear_combination -hexRoot_poly

lemma hexRotation_basis (i : Fin 2) :
    planeRotation hexRoot (hexLattice.basis i : Plane) ∈ hexLattice.carrier := by
  fin_cases i
  · have h : planeRotation hexRoot (hexLattice.basis 0 : Plane) =
        (hexLattice.basis 1 : Plane) := by
      apply coordinateIsometry.injective
      simp
    change planeRotation hexRoot (hexLattice.basis (0 : Fin 2) : Plane) ∈
      hexLattice.carrier
    rw [h]
    exact (hexLattice.basis 1).property
  · have h : planeRotation hexRoot (hexLattice.basis 1 : Plane) =
        (hexLattice.basis 1 : Plane) - (hexLattice.basis 0 : Plane) := by
      apply coordinateIsometry.injective
      simp
      linear_combination hexRoot_poly
    change planeRotation hexRoot (hexLattice.basis (1 : Fin 2) : Plane) ∈
      hexLattice.carrier
    rw [h]
    exact hexLattice.carrier.sub_mem
      (hexLattice.basis 1).property (hexLattice.basis 0).property

lemma hexRotation_inv_basis (i : Fin 2) :
    (planeRotation hexRoot)⁻¹ (hexLattice.basis i : Plane) ∈ hexLattice.carrier := by
  fin_cases i
  · have h : (planeRotation hexRoot)⁻¹ (hexLattice.basis 0 : Plane) =
        (hexLattice.basis 0 : Plane) - (hexLattice.basis 1 : Plane) := by
      apply coordinateIsometry.injective
      rw [planeRotation_inv, coordinateIsometry_planeRotation,
        coordinateIsometry_hexLattice_basis_zero, map_sub,
        coordinateIsometry_hexLattice_basis_zero,
        coordinateIsometry_hexLattice_basis_one, hexRoot_coe_inv]
      ring
    change (planeRotation hexRoot)⁻¹
      (hexLattice.basis (0 : Fin 2) : Plane) ∈ hexLattice.carrier
    rw [h]
    exact hexLattice.carrier.sub_mem
      (hexLattice.basis 0).property (hexLattice.basis 1).property
  · have h : (planeRotation hexRoot)⁻¹ (hexLattice.basis 1 : Plane) =
        (hexLattice.basis 0 : Plane) := by
      apply coordinateIsometry.injective
      rw [planeRotation_inv, coordinateIsometry_planeRotation,
        coordinateIsometry_hexLattice_basis_one,
        coordinateIsometry_hexLattice_basis_zero, hexRoot_coe_inv]
      linear_combination -hexRoot_poly
    change (planeRotation hexRoot)⁻¹
      (hexLattice.basis (1 : Fin 2) : Plane) ∈ hexLattice.carrier
    rw [h]
    exact (hexLattice.basis 0).property

lemma hexRotation_mem_stabilizer :
    planeRotation hexRoot ∈ latticeStabilizer hexLattice :=
  mem_latticeStabilizer_of_basis hexLattice (planeRotation hexRoot)
    hexRotation_basis hexRotation_inv_basis

lemma squareRotation_basis (i : Fin 2) :
    planeRotation squareRoot
      (RankTwoLattice.standardLattice.basis i : Plane) ∈
        RankTwoLattice.standardLattice.carrier := by
  fin_cases i
  · have h : planeRotation squareRoot
        (RankTwoLattice.standardLattice.basis 0 : Plane) =
          (RankTwoLattice.standardLattice.basis 1 : Plane) := by
      apply coordinateIsometry.injective
      rw [coordinateIsometry_planeRotation,
        coordinateIsometry_squareLattice_basis_zero,
        coordinateIsometry_squareLattice_basis_one]
      simp [squareRoot]
    change planeRotation squareRoot
      (RankTwoLattice.standardLattice.basis (0 : Fin 2) : Plane) ∈
        RankTwoLattice.standardLattice.carrier
    rw [h]
    exact (RankTwoLattice.standardLattice.basis 1).property
  · have h : planeRotation squareRoot
        (RankTwoLattice.standardLattice.basis 1 : Plane) =
          -(RankTwoLattice.standardLattice.basis 0 : Plane) := by
      apply coordinateIsometry.injective
      rw [coordinateIsometry_planeRotation,
        coordinateIsometry_squareLattice_basis_one, map_neg,
        coordinateIsometry_squareLattice_basis_zero]
      simp [squareRoot, Complex.I_mul_I]
    change planeRotation squareRoot
      (RankTwoLattice.standardLattice.basis (1 : Fin 2) : Plane) ∈
        RankTwoLattice.standardLattice.carrier
    rw [h]
    exact RankTwoLattice.standardLattice.carrier.neg_mem
      (RankTwoLattice.standardLattice.basis 0).property

lemma squareRotation_inv_basis (i : Fin 2) :
    (planeRotation squareRoot)⁻¹
      (RankTwoLattice.standardLattice.basis i : Plane) ∈
        RankTwoLattice.standardLattice.carrier := by
  fin_cases i
  · have h : (planeRotation squareRoot)⁻¹
        (RankTwoLattice.standardLattice.basis 0 : Plane) =
          -(RankTwoLattice.standardLattice.basis 1 : Plane) := by
      apply coordinateIsometry.injective
      rw [planeRotation_inv, coordinateIsometry_planeRotation,
        coordinateIsometry_squareLattice_basis_zero, map_neg,
        coordinateIsometry_squareLattice_basis_one]
      rw [Circle.coe_inv]
      simp [squareRoot, Complex.inv_I]
    change (planeRotation squareRoot)⁻¹
      (RankTwoLattice.standardLattice.basis (0 : Fin 2) : Plane) ∈
        RankTwoLattice.standardLattice.carrier
    rw [h]
    exact RankTwoLattice.standardLattice.carrier.neg_mem
      (RankTwoLattice.standardLattice.basis 1).property
  · have h : (planeRotation squareRoot)⁻¹
        (RankTwoLattice.standardLattice.basis 1 : Plane) =
          (RankTwoLattice.standardLattice.basis 0 : Plane) := by
      apply coordinateIsometry.injective
      rw [planeRotation_inv, coordinateIsometry_planeRotation,
        coordinateIsometry_squareLattice_basis_one,
        coordinateIsometry_squareLattice_basis_zero]
      rw [Circle.coe_inv]
      simp [squareRoot, Complex.inv_I]
    change (planeRotation squareRoot)⁻¹
      (RankTwoLattice.standardLattice.basis (1 : Fin 2) : Plane) ∈
        RankTwoLattice.standardLattice.carrier
    rw [h]
    exact (RankTwoLattice.standardLattice.basis 0).property

lemma squareRotation_mem_stabilizer :
    planeRotation squareRoot ∈
      latticeStabilizer RankTwoLattice.standardLattice :=
  mem_latticeStabilizer_of_basis RankTwoLattice.standardLattice
    (planeRotation squareRoot) squareRotation_basis squareRotation_inv_basis

/-- The cyclic subgroup generated by a lattice stabilizer preserves the lattice. -/
lemma zpowers_latticePreserving
    (L : RankTwoLattice Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hR : R ∈ latticeStabilizer L) :
    LatticePreservingPointGroup L (Subgroup.zpowers R) := by
  intro A t ht
  have hsub : Subgroup.zpowers R ≤ latticeStabilizer L :=
    Subgroup.zpowers_le.mpr hR
  exact ((hsub A.property) t).mp ht

lemma squareRoot_sq_order : orderOf (squareRoot ^ 2) = 2 := by
  rw [orderOf_pow' (x := squareRoot) (n := 2) (by norm_num), squareRoot_order]
  norm_num

lemma hexRoot_sq_order : orderOf (hexRoot ^ 2) = 3 := by
  rw [orderOf_pow' (x := hexRoot) (n := 2) (by norm_num), hexRoot_order]
  norm_num

/-- The common transparent model generated by one finite lattice rotation. -/
def cyclicRotationModel
    (L : RankTwoLattice Plane) (a : Circle)
    (ha : planeRotation a ∈ latticeStabilizer L)
    {q : ℕ} (horder : orderOf a = q) (hq : q ≠ 0) : PlaneGroup := by
  letI : Finite (Subgroup.zpowers (planeRotation a)) :=
    Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers, planeRotation_order, horder]
      exact hq)
  exact symmorphicPlaneGroup L (Subgroup.zpowers (planeRotation a))
    (zpowers_latticePreserving L (planeRotation a) ha)

/-- The `p1` model: the square lattice with trivial point group. -/
def p1Model : PlaneGroup :=
  cyclicRotationModel (q := 1) RankTwoLattice.standardLattice 1
    (by simpa only [planeRotation_one] using
      (latticeStabilizer RankTwoLattice.standardLattice).one_mem)
    (by simp) (by norm_num)

/-- The `p2` model: the square lattice with its half turn. -/
def p2Model : PlaneGroup :=
  cyclicRotationModel RankTwoLattice.standardLattice (squareRoot ^ 2)
    (by
      change planeRotationHom (squareRoot ^ 2) ∈
        latticeStabilizer RankTwoLattice.standardLattice
      rw [map_pow]
      exact (latticeStabilizer RankTwoLattice.standardLattice).pow_mem
        squareRotation_mem_stabilizer 2)
    squareRoot_sq_order (by norm_num)

/-- The `p3` model: the triangular lattice with its third turn. -/
def p3Model : PlaneGroup :=
  cyclicRotationModel hexLattice (hexRoot ^ 2)
    (by
      change planeRotationHom (hexRoot ^ 2) ∈ latticeStabilizer hexLattice
      rw [map_pow]
      exact (latticeStabilizer hexLattice).pow_mem hexRotation_mem_stabilizer 2)
    hexRoot_sq_order (by norm_num)

/-- The `p4` model: the square lattice with its quarter turn. -/
def p4Model : PlaneGroup :=
  cyclicRotationModel RankTwoLattice.standardLattice squareRoot
    squareRotation_mem_stabilizer squareRoot_order (by norm_num)

/-- The `p6` model: the triangular lattice with its sixth turn. -/
def p6Model : PlaneGroup :=
  cyclicRotationModel hexLattice hexRoot hexRotation_mem_stabilizer hexRoot_order (by norm_num)

theorem cyclicRotationModel_pointGroup
    (L : RankTwoLattice Plane) (a : Circle)
    (ha : planeRotation a ∈ latticeStabilizer L)
    {q : ℕ} (horder : orderOf a = q) (hq : q ≠ 0) :
    pointGroup (cyclicRotationModel L a ha horder hq).carrier =
      Subgroup.zpowers (planeRotation a) := by
  have hc : (cyclicRotationModel L a ha horder hq).carrier =
      symmorphicCarrier L (Subgroup.zpowers (planeRotation a))
        (zpowers_latticePreserving L (planeRotation a) ha) := rfl
  rw [hc]
  exact symmorphicCarrier_pointGroup L (Subgroup.zpowers (planeRotation a))
    (zpowers_latticePreserving L (planeRotation a) ha)

theorem cyclicRotationModel_pointGroup_card
    (L : RankTwoLattice Plane) (a : Circle)
    (ha : planeRotation a ∈ latticeStabilizer L)
    {q : ℕ} (horder : orderOf a = q) (hq : q ≠ 0) :
    Nat.card (pointGroup (cyclicRotationModel L a ha horder hq).carrier) = q := by
  rw [cyclicRotationModel_pointGroup, Nat.card_zpowers, planeRotation_order, horder]

/-- Every element of the cyclic rotation subgroup has determinant one. -/
lemma det_eq_one_of_mem_zpowers_planeRotation
    (a : Circle) (A : Plane ≃ₗᵢ[ℝ] Plane)
    (hA : A ∈ Subgroup.zpowers (planeRotation a)) :
    LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 := by
  rw [Subgroup.mem_zpowers_iff] at hA
  obtain ⟨k, rfl⟩ := hA
  change LinearMap.det
    (((planeRotationHom a) ^ k).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1
  rw [← map_zpow planeRotationHom a k]
  exact planeRotation_det (a ^ k)

/-- A cyclic rotation model has no orientation-reversing point-group elements. -/
theorem cyclicRotationModel_hasNoReflections
    (L : RankTwoLattice Plane) (a : Circle)
    (ha : planeRotation a ∈ latticeStabilizer L)
    {q : ℕ} (horder : orderOf a = q) (hq : q ≠ 0) :
    ∀ p : pointGroup (cyclicRotationModel L a ha horder hq).carrier,
      p ∈ orientationPreservingPointGroup
        (cyclicRotationModel L a ha horder hq) := by
  intro p
  have hp : (p : Plane ≃ₗᵢ[ℝ] Plane) ∈
      Subgroup.zpowers (planeRotation a) := by
    have hle : pointGroup (cyclicRotationModel L a ha horder hq).carrier ≤
        Subgroup.zpowers (planeRotation a) := by
      rw [cyclicRotationModel_pointGroup L a ha horder hq]
    exact hle p.property
  change 0 < ((pointGroupDet
    (cyclicRotationModel L a ha horder hq) p : ℝˣ) : ℝ)
  rw [pointGroupDet_apply,
    det_eq_one_of_mem_zpowers_planeRotation a (p : Plane ≃ₗᵢ[ℝ] Plane) hp]
  norm_num

@[simp] theorem p1Model_pointGroup_card :
    Nat.card (pointGroup p1Model.carrier) = 1 := by
  unfold p1Model
  apply cyclicRotationModel_pointGroup_card

@[simp] theorem p2Model_pointGroup_card :
    Nat.card (pointGroup p2Model.carrier) = 2 := by
  unfold p2Model
  apply cyclicRotationModel_pointGroup_card

@[simp] theorem p3Model_pointGroup_card :
    Nat.card (pointGroup p3Model.carrier) = 3 := by
  unfold p3Model
  apply cyclicRotationModel_pointGroup_card

@[simp] theorem p4Model_pointGroup_card :
    Nat.card (pointGroup p4Model.carrier) = 4 := by
  unfold p4Model
  apply cyclicRotationModel_pointGroup_card

@[simp] theorem p6Model_pointGroup_card :
    Nat.card (pointGroup p6Model.carrier) = 6 := by
  unfold p6Model
  apply cyclicRotationModel_pointGroup_card

/-- The standard reflection-free model indexed by its crystallographic rotation order. -/
def rotationModel : CrystallographicOrder → PlaneGroup
  | .one => p1Model
  | .two => p2Model
  | .three => p3Model
  | .four => p4Model
  | .six => p6Model

/-- The standard rotation model has the point-group cardinality named by its index. -/
@[simp]
theorem rotationModel_pointGroup_card (q : CrystallographicOrder) :
    Nat.card (pointGroup (rotationModel q).carrier) = q.toNat := by
  cases q <;> simp [rotationModel, CrystallographicOrder.toNat]

/-- Every point element of a standard rotation model preserves orientation. -/
theorem rotationModel_all_orientationPreserving (q : CrystallographicOrder) :
    ∀ p : pointGroup (rotationModel q).carrier,
      p ∈ orientationPreservingPointGroup (rotationModel q) := by
  cases q <;> simp only [rotationModel] <;>
    apply cyclicRotationModel_hasNoReflections

end
end WallpaperGroups
