/-
Copyright (c) 2026 Shengyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyi Wang
-/
import WallpaperGroups.Restriction.LatticeNormalForms
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Integral normal forms for lattice reflections

This file classifies determinant `-1` involutions of a rank-two integer lattice
up to an integral change of basis.  It then applies that classification to the
lattice action of an orientation-reversing point-group element and computes the
fixed, anti-fixed, and norm directions used by the one-reflection classification.
-/

set_option autoImplicit false

open Matrix


namespace WallpaperGroups
namespace IntegralReflection

noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

def basisFromCoprime (b : Module.Basis (Fin 2) ℤ M)
    (u0 u1 : ℤ) (hu : Int.gcd u0 u1 = 1) : Module.Basis (Fin 2) ℤ M := by
  let p := Int.gcdA u0 u1
  let q := Int.gcdB u0 u1
  let P : Matrix (Fin 2) (Fin 2) ℤ := !![u0, -q; u1, p]
  have hbez : u0 * p + u1 * q = 1 := by
    simpa [p, q, hu] using (Int.gcd_eq_gcd_ab u0 u1).symm
  have hdet : P.det = 1 := by
    simp [P, Matrix.det_fin_two]
    linarith
  let e : M ≃ₗ[ℤ] M := Matrix.toLinearEquiv b P (by simp [hdet])
  exact b.map e

set_option linter.flexible false in
lemma basisFromCoprime_zero (b : Module.Basis (Fin 2) ℤ M)
    (u0 u1 : ℤ) (hu : Int.gcd u0 u1 = 1) :
    basisFromCoprime b u0 u1 hu 0 = u0 • b 0 + u1 • b 1 := by
  simp [basisFromCoprime, Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change (inferInstance : Module ℤ M).smul u0 (b 0) +
      (inferInstance : Module ℤ M).smul u1 (b 1) = _
  rw [int_smul_eq_zsmul, int_smul_eq_zsmul]

set_option linter.flexible false in
lemma basisFromCoprime_one (b : Module.Basis (Fin 2) ℤ M)
    (u0 u1 : ℤ) (hu : Int.gcd u0 u1 = 1) :
    basisFromCoprime b u0 u1 hu 1 =
      -(Int.gcdB u0 u1) • b 0 + (Int.gcdA u0 u1) • b 1 := by
  simp [basisFromCoprime, Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change -((inferInstance : Module ℤ M).smul (Int.gcdB u0 u1) (b 0)) +
      (inferInstance : Module ℤ M).smul (Int.gcdA u0 u1) (b 1) = _
  rw [int_smul_eq_zsmul, int_smul_eq_zsmul]

lemma trace_eq_zero_of_sq_eq_one_of_det_eq_neg_one
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hsq : A ^ 2 = 1) (hdet : A.det = -1) :
    A.trace = 0 := by
  have hc := WallpaperGroups.cayley_hamilton A
  rw [hsq, hdet] at hc
  have hs : A.trace • A = 0 := by
    simp only [neg_one_smul] at hc
    abel_nf at hc
    have hneg : -(A.trace • A) = 0 := by
      simpa only [smul_smul, neg_one_mul, neg_smul] using hc
    exact neg_eq_zero.mp hneg
  by_contra ht
  have hA0 : A = 0 := by
    apply smul_right_injective (Matrix (Fin 2) (Fin 2) ℤ) ht
    simpa using hs
  rw [hA0, Matrix.det_zero] at hdet
  norm_num at hdet

def integralFixedVector (A : Matrix (Fin 2) (Fin 2) ℤ) : Fin 2 → ℤ :=
  if A 0 1 = 0 ∧ A 0 0 = 1 then ![2, A 1 0] else ![A 0 1, 1 - A 0 0]

lemma integralFixedVector_ne_zero (A : Matrix (Fin 2) (Fin 2) ℤ) :
    integralFixedVector A ≠ 0 := by
  intro h
  by_cases hspecial : A 0 1 = 0 ∧ A 0 0 = 1
  · have h0 := congrFun h 0
    simp [integralFixedVector, hspecial] at h0
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [integralFixedVector, hspecial] at h0 h1
    apply hspecial
    omega

lemma mulVec_integralFixedVector
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (htrace : A.trace = 0) (hdet : A.det = -1) :
    A *ᵥ integralFixedVector A = integralFixedVector A := by
  have ht : A 0 0 + A 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using htrace
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = -1 := by
    simpa [Matrix.det_fin_two] using hdet
  by_cases hspecial : A 0 1 = 0 ∧ A 0 0 = 1
  · have hd1 : A 1 1 = -1 := by omega
    funext i
    fin_cases i <;>
      simp [integralFixedVector, hspecial, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hd1]
    all_goals ring
  · have hdneg : A 1 1 = -A 0 0 := by omega
    rw [hdneg] at hd
    funext i
    fin_cases i <;>
      simp [integralFixedVector, hspecial, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hdneg] <;>
      nlinarith

def shearBasis (b : Module.Basis (Fin 2) ℤ M) (n : ℤ) :
    Module.Basis (Fin 2) ℤ M := by
  let P : Matrix (Fin 2) (Fin 2) ℤ := !![1, n; 0, 1]
  have hdet : P.det = 1 := by simp [P, Matrix.det_fin_two]
  let e : M ≃ₗ[ℤ] M := Matrix.toLinearEquiv b P (by simp [hdet])
  exact b.map e

set_option linter.flexible false in
lemma shearBasis_zero (b : Module.Basis (Fin 2) ℤ M) (n : ℤ) :
    shearBasis b n 0 = b 0 := by
  simp [shearBasis, Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change (inferInstance : Module ℤ M).smul 1 (b 0) +
      (inferInstance : Module ℤ M).smul 0 (b 1) = _
  rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
  simp

set_option linter.flexible false in
lemma shearBasis_one (b : Module.Basis (Fin 2) ℤ M) (n : ℤ) :
    shearBasis b n 1 = n • b 0 + b 1 := by
  simp [shearBasis, Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change (inferInstance : Module ℤ M).smul n (b 0) +
      (inferInstance : Module ℤ M).smul 1 (b 1) = _
  rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
  simp

/-- The two integral conjugacy classes of rank-two lattice reflections. -/
inductive ReflectionLatticeKind
  | primitive
  | centered
  deriving DecidableEq

/-- The primitive and centered reflection matrices, written in column convention. -/
def reflectionLatticeMatrix : ReflectionLatticeKind → Matrix (Fin 2) (Fin 2) ℤ
  | .primitive => !![1, 0; 0, -1]
  | .centered => !![1, 1; 0, -1]

lemma toMatrix_eq_reflectionLatticeMatrix
    (b : Module.Basis (Fin 2) ℤ M) (f : M ≃ₗ[ℤ] M) (kind : ReflectionLatticeKind)
    (h0 : f (b 0) = b 0)
    (h1 : f (b 1) = (match kind with
      | .primitive => -(b 1)
      | .centered => b 0 - b 1)) :
    LinearMap.toMatrix b b f.toLinearMap = reflectionLatticeMatrix kind := by
  ext i j
  cases kind <;> fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, reflectionLatticeMatrix, h0, h1]

lemma exists_fixed_basis
    (b : Module.Basis (Fin 2) ℤ M) (f : M ≃ₗ[ℤ] M)
    (hsq : (LinearMap.toMatrix b b f.toLinearMap) ^ 2 = 1)
    (hdet : (LinearMap.toMatrix b b f.toLinearMap).det = -1) :
    ∃ b' : Module.Basis (Fin 2) ℤ M, f (b' 0) = b' 0 := by
  let A := LinearMap.toMatrix b b f.toLinearMap
  have htrace : A.trace = 0 :=
    trace_eq_zero_of_sq_eq_one_of_det_eq_neg_one A hsq hdet
  let x := integralFixedVector A
  have hx0 : x ≠ 0 := integralFixedVector_ne_zero A
  have hxcoords : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_cases h0 : x 0 = 0
    · right
      intro h1
      apply hx0
      funext i
      fin_cases i <;> simp [h0, h1]
    · exact Or.inl h0
  have hgpos : 0 < Int.gcd (x 0) (x 1) := by
    rcases hxcoords with hx | hx
    · exact Int.gcd_pos_of_ne_zero_left _ hx
    · exact Int.gcd_pos_of_ne_zero_right _ hx
  let g := Int.gcd (x 0) (x 1)
  have hgpos' : 0 < g := hgpos
  obtain ⟨u0, u1, hu, hx0eq, hx1eq⟩ := Int.exists_gcd_one hgpos
  change x 0 = u0 * (g : ℤ) at hx0eq
  change x 1 = u1 * (g : ℤ) at hx1eq
  let u : Fin 2 → ℤ := ![u0, u1]
  have hx_eq : x = (g : ℤ) • u := by
    funext i
    fin_cases i
    · change x 0 = (g : ℤ) * u0
      rw [hx0eq]
      ring
    · change x 1 = (g : ℤ) * u1
      rw [hx1eq]
      ring
  have hufix : A *ᵥ u = u := by
    have hxfix : A *ᵥ x = x := mulVec_integralFixedVector A htrace hdet
    have hscaled : (g : ℤ) • (A *ᵥ u) = (g : ℤ) • u := by
      rw [← Matrix.mulVec_smul, ← hx_eq, hxfix, hx_eq]
    apply smul_right_injective (Fin 2 → ℤ) (by exact_mod_cast hgpos'.ne')
    exact hscaled
  let b' := basisFromCoprime b u0 u1 hu
  refine ⟨b', ?_⟩
  apply b.equivFun.injective
  have hmatrix := LinearMap.toMatrix_mulVec_repr b b f.toLinearMap (b' 0)
  have hrepr : b.equivFun (b' 0) = u := by
    funext i
    fin_cases i <;>
      simp [b', u, basisFromCoprime_zero]
  change A *ᵥ b.equivFun (b' 0) = b.equivFun (f (b' 0)) at hmatrix
  rw [hrepr] at hmatrix
  rw [hufix] at hmatrix
  exact hmatrix.symm.trans hrepr.symm

/-- A determinant `-1` involution of a rank-two integer lattice has one of the
two reflection matrices after an integral change of basis. -/
theorem exists_integralReflectionNormalForm
    (b : Module.Basis (Fin 2) ℤ M) (f : M ≃ₗ[ℤ] M)
    (hsq : (LinearMap.toMatrix b b f.toLinearMap) ^ 2 = 1)
    (hdet : (LinearMap.toMatrix b b f.toLinearMap).det = -1) :
    ∃ (kind : ReflectionLatticeKind) (b' : Module.Basis (Fin 2) ℤ M),
      LinearMap.toMatrix b' b' f.toLinearMap = reflectionLatticeMatrix kind := by
  obtain ⟨b0, hb0⟩ := exists_fixed_basis b f hsq hdet
  let D := LinearMap.toMatrix b0 b0 f.toLinearMap
  let k : ℤ := b0.equivFun (f (b0 1)) 0
  let l : ℤ := b0.equivFun (f (b0 1)) 1
  have hf1 : f (b0 1) = k • b0 0 + l • b0 1 := by
    have hsum := b0.sum_equivFun (f (b0 1))
    rw [Fin.sum_univ_two] at hsum
    calc
      f (b0 1) =
          (inferInstance : Module ℤ M).smul k (b0 0) +
            (inferInstance : Module ℤ M).smul l (b0 1) := by
        dsimp [k, l]
        exact hsum.symm
      _ = k • b0 0 + l • b0 1 := by
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
  have hD00 : D 0 0 = 1 := by
    simp [D, LinearMap.toMatrix_apply, hb0]
  have hD10 : D 1 0 = 0 := by
    simp [D, LinearMap.toMatrix_apply, hb0]
  have hD11 : D 1 1 = l := by
    simp [D, l, LinearMap.toMatrix_apply]
  have hdetD : D.det = -1 := by
    calc
      D.det = (LinearMap.det f.toLinearMap) :=
        LinearMap.det_toMatrix b0 f.toLinearMap
      _ = (LinearMap.toMatrix b b f.toLinearMap).det :=
        (LinearMap.det_toMatrix b f.toLinearMap).symm
      _ = -1 := hdet
  have hl : l = -1 := by
    rw [Matrix.det_fin_two, hD00, hD10, hD11] at hdetD
    simpa using hdetD
  have hf1' : f (b0 1) = k • b0 0 - b0 1 := by
    rw [hf1, hl]
    simp only [neg_one_zsmul, sub_eq_add_neg]
  let n : ℤ := -(k / 2)
  let r : ℤ := k % 2
  have hkn : k + 2 * n = r := by
    have hdiv := Int.emod_add_mul_ediv k 2
    dsimp [n, r]
    omega
  let b' := shearBasis b0 n
  have hb'0 : f (b' 0) = b' 0 := by
    simp [b', shearBasis_zero, hb0]
  have hb'1 : f (b' 1) = r • b' 0 - b' 1 := by
    rw [show b' 1 = n • b0 0 + b0 1 by simp [b', shearBasis_one]]
    rw [map_add, map_zsmul, hb0, hf1']
    rw [show b' 0 = b0 0 by simp [b', shearBasis_zero]]
    have hcoeff : n + k = r - n := by omega
    calc
      n • b0 0 + (k • b0 0 - b0 1) = (n + k) • b0 0 - b0 1 := by
        rw [add_zsmul]
        abel
      _ = (r - n) • b0 0 - b0 1 := by rw [hcoeff]
      _ = r • b0 0 - (n • b0 0 + b0 1) := by
        rw [sub_zsmul]
        abel
  rcases Int.emod_two_eq_zero_or_one k with hr | hr
  · refine ⟨.primitive, b', ?_⟩
    apply toMatrix_eq_reflectionLatticeMatrix b' f .primitive hb'0
    simpa [r, hr] using hb'1
  · refine ⟨.centered, b', ?_⟩
    apply toMatrix_eq_reflectionLatticeMatrix b' f .centered hb'0
    simpa [r, hr] using hb'1

end
end IntegralReflection

open EuclideanMotion

noncomputable section

namespace PlaneGroup

/-- Lattice translations fixed by the point element `s`. -/
def reflectionFixedSubmodule (G : PlaneGroup)
    (s : pointGroup G.carrier) : Submodule ℤ G.translationLattice.carrier :=
  LinearMap.ker ((G.latticeAction s).toLinearMap - LinearMap.id)

/-- Lattice translations sent to their negatives by the point element `s`. -/
def reflectionAntiFixedSubmodule (G : PlaneGroup)
    (s : pointGroup G.carrier) : Submodule ℤ G.translationLattice.carrier :=
  LinearMap.ker ((G.latticeAction s).toLinearMap + LinearMap.id)

/-- The reflection norm `t ↦ t + s t` on the translation lattice. -/
def reflectionNormMap (G : PlaneGroup)
    (s : pointGroup G.carrier) :
    G.translationLattice.carrier →ₗ[ℤ] G.translationLattice.carrier :=
  LinearMap.id + (G.latticeAction s).toLinearMap

/-- The range of the reflection norm map. -/
def reflectionNormRange (G : PlaneGroup)
    (s : pointGroup G.carrier) : Submodule ℤ G.translationLattice.carrier :=
  LinearMap.range (reflectionNormMap G s)

@[simp] lemma mem_reflectionFixedSubmodule_iff
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (t : G.translationLattice.carrier) :
    t ∈ reflectionFixedSubmodule G s ↔ G.latticeAction s t = t := by
  simp [reflectionFixedSubmodule, sub_eq_zero]

@[simp] lemma mem_reflectionAntiFixedSubmodule_iff
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (t : G.translationLattice.carrier) :
    t ∈ reflectionAntiFixedSubmodule G s ↔ G.latticeAction s t = -t := by
  simp [reflectionAntiFixedSubmodule, add_eq_zero_iff_eq_neg]

@[simp] lemma reflectionNormMap_apply
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (t : G.translationLattice.carrier) :
    reflectionNormMap G s t = t + G.latticeAction s t := by
  rfl

lemma mem_reflectionNormRange_iff
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (t : G.translationLattice.carrier) :
    t ∈ reflectionNormRange G s ↔
      ∃ u, u + G.latticeAction s u = t := by
  simp [reflectionNormRange]

lemma reversing_integral_det_eq_neg_one
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G) :
    (G.latticeActionMatrix s).det = -1 := by
  have hsquare : s ^ 2 = 1 := pointGroup_reversing_sq G s hs
  have hunit : pointGroupDet G s ^ 2 = 1 := by
    rw [← map_pow, hsquare, map_one]
  have hval := congrArg Units.val hunit
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at hval
  have hneg := pointGroup_det_neg_of_not_mem_orientationPreserving G s hs
  have hreal : LinearMap.det
      ((s : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1 := by
    have hsqdet : LinearMap.det
        ((s : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) ^ 2 = 1 := by
      simpa only [pointGroupDet_apply] using hval
    nlinarith
  have hc := G.det_cast s
  exact_mod_cast hc.trans hreal

lemma reversing_latticeActionMatrix_sq
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G) :
    G.latticeActionMatrix s ^ 2 = 1 := by
  have hsquare : s ^ 2 = 1 := pointGroup_reversing_sq G s hs
  have hu : G.integralRepresentation s ^ 2 = 1 := by
    rw [← map_pow, hsquare, map_one]
  exact congrArg Units.val hu

/-- A basis in which an orientation-reversing lattice action has one of the two
integral reflection matrices. -/
structure ReflectionLatticeNormalForm
    (G : PlaneGroup) (s : pointGroup G.carrier) where
  kind : IntegralReflection.ReflectionLatticeKind
  basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier
  matrix_eq : LinearMap.toMatrix basis basis (G.latticeAction s).toLinearMap =
    IntegralReflection.reflectionLatticeMatrix kind

/-- Every orientation-reversing point element admits an integral reflection
normal form on the translation lattice. -/
theorem exists_reflectionLatticeNormalForm
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G) :
    Nonempty (ReflectionLatticeNormalForm G s) := by
  obtain ⟨kind, b, hb⟩ := IntegralReflection.exists_integralReflectionNormalForm
    G.translationLattice.basis (G.latticeAction s)
    (G.reversing_latticeActionMatrix_sq s hs)
    (G.reversing_integral_det_eq_neg_one s hs)
  exact ⟨⟨kind, b, hb⟩⟩

namespace ReflectionLatticeNormalForm

variable {G : PlaneGroup} {s : pointGroup G.carrier}

lemma action_coordinates (N : ReflectionLatticeNormalForm G s)
    (t : G.translationLattice.carrier) :
    ⇑(N.basis.repr (G.latticeAction s t)) =
      IntegralReflection.reflectionLatticeMatrix N.kind *ᵥ ⇑(N.basis.repr t) := by
  have h := LinearMap.toMatrix_mulVec_repr N.basis N.basis
    (G.latticeAction s).toLinearMap t
  rw [N.matrix_eq] at h
  exact h.symm

/-- In either normal form, the fixed direction is the first coordinate axis. -/
lemma fixed_iff_second_coordinate_zero (N : ReflectionLatticeNormalForm G s)
    (t : G.translationLattice.carrier) :
    G.latticeAction s t = t ↔ N.basis.repr t 1 = 0 := by
  constructor
  · intro ht
    have hcoord := congrFun (N.action_coordinates t) 1
    rw [ht] at hcoord
    cases hkind : N.kind <;>
      simp [hkind, IntegralReflection.reflectionLatticeMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] at hcoord <;>
      omega
  · intro ht
    apply N.basis.repr.injective
    ext i
    have hcoord := congrFun (N.action_coordinates t) i
    rw [hcoord]
    cases hkind : N.kind <;> fin_cases i <;>
      simp [IntegralReflection.reflectionLatticeMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, ht]

/-- Coordinate description of the anti-fixed direction in either normal form. -/
lemma antiFixed_iff (N : ReflectionLatticeNormalForm G s)
    (t : G.translationLattice.carrier) :
    G.latticeAction s t = -t ↔
      2 * N.basis.repr t 0 +
        (match N.kind with
          | .primitive => 0
          | .centered => N.basis.repr t 1) = 0 := by
  constructor
  · intro ht
    have hcoord := congrFun (N.action_coordinates t) 0
    rw [ht] at hcoord
    cases hkind : N.kind <;>
      simp [hkind, IntegralReflection.reflectionLatticeMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] at hcoord ⊢ <;>
      omega
  · intro ht
    apply N.basis.repr.injective
    ext i
    have hcoord := congrFun (N.action_coordinates t) i
    rw [hcoord]
    cases hkind : N.kind <;> fin_cases i <;>
      simp [hkind, IntegralReflection.reflectionLatticeMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] at ht ⊢ <;>
      omega

lemma norm_coordinates (N : ReflectionLatticeNormalForm G s)
    (t : G.translationLattice.carrier) :
    ⇑(N.basis.repr (t + G.latticeAction s t)) =
      match N.kind with
      | .primitive => ![2 * N.basis.repr t 0, 0]
      | .centered => ![2 * N.basis.repr t 0 + N.basis.repr t 1, 0] := by
  ext i
  have hcoord := congrFun (N.action_coordinates t) i
  simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  rw [hcoord]
  cases hkind : N.kind <;> fin_cases i <;>
    simp [IntegralReflection.reflectionLatticeMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    ring

/-- In the primitive form, a fixed vector is a norm exactly when its first
coordinate is even. -/
lemma primitive_mem_reflectionNormRange_iff
    (N : ReflectionLatticeNormalForm G s)
    (hkind : N.kind = .primitive)
    (t : G.translationLattice.carrier) :
    t ∈ reflectionNormRange G s ↔
      t ∈ reflectionFixedSubmodule G s ∧ Even (N.basis.repr t 0) := by
  rw [mem_reflectionNormRange_iff]
  constructor
  · rintro ⟨u, hu⟩
    have hn := N.norm_coordinates u
    rw [hkind, hu] at hn
    constructor
    · rw [mem_reflectionFixedSubmodule_iff,
          N.fixed_iff_second_coordinate_zero]
      have h1 := congrFun hn 1
      simpa using h1
    · have h0 := congrFun hn 0
      refine ⟨N.basis.repr u 0, ?_⟩
      simp only [Matrix.cons_val_zero] at h0
      omega
  · rintro ⟨htfix, ⟨z, hz⟩⟩
    let u := N.basis.equivFun.symm ![z, 0]
    refine ⟨u, ?_⟩
    apply N.basis.repr.injective
    ext i
    have hn := congrFun (N.norm_coordinates u) i
    rw [hkind] at hn
    have hucoords : N.basis.equivFun u = ![z, 0] := by
      exact N.basis.equivFun.apply_symm_apply _
    have ht1 : N.basis.repr t 1 = 0 :=
      (N.fixed_iff_second_coordinate_zero t).mp
        (mem_reflectionFixedSubmodule_iff G s t |>.mp htfix)
    fin_cases i
    · rw [hn]
      change 2 * N.basis.equivFun u 0 = N.basis.repr t 0
      rw [hucoords]
      simp only [Matrix.cons_val_zero]
      omega
    · rw [hn]
      simpa using ht1.symm

/-- In the centered form, every fixed vector is a reflection norm. -/
lemma centered_mem_reflectionNormRange_iff
    (N : ReflectionLatticeNormalForm G s)
    (hkind : N.kind = .centered)
    (t : G.translationLattice.carrier) :
    t ∈ reflectionNormRange G s ↔
      t ∈ reflectionFixedSubmodule G s := by
  rw [mem_reflectionNormRange_iff]
  constructor
  · rintro ⟨u, hu⟩
    rw [mem_reflectionFixedSubmodule_iff,
      N.fixed_iff_second_coordinate_zero]
    have hn := N.norm_coordinates u
    rw [hkind, hu] at hn
    have h1 := congrFun hn 1
    simpa using h1
  · intro htfix
    let u := N.basis.equivFun.symm ![0, N.basis.repr t 0]
    refine ⟨u, ?_⟩
    apply N.basis.repr.injective
    ext i
    have hn := congrFun (N.norm_coordinates u) i
    rw [hkind] at hn
    have hucoords : N.basis.equivFun u = ![0, N.basis.repr t 0] := by
      exact N.basis.equivFun.apply_symm_apply _
    have ht1 : N.basis.repr t 1 = 0 :=
      (N.fixed_iff_second_coordinate_zero t).mp
        (mem_reflectionFixedSubmodule_iff G s t |>.mp htfix)
    fin_cases i
    · rw [hn]
      change 2 * N.basis.equivFun u 0 + N.basis.equivFun u 1 =
        N.basis.repr t 0
      rw [hucoords]
      simp
    · rw [hn]
      simpa using ht1.symm

lemma centered_fixed_is_reflectionNorm
    (N : ReflectionLatticeNormalForm G s)
    (hkind : N.kind = .centered)
    {t : G.translationLattice.carrier}
    (ht : t ∈ reflectionFixedSubmodule G s) :
    ∃ u, u + G.latticeAction s u = t := by
  rw [← mem_reflectionNormRange_iff]
  exact (N.centered_mem_reflectionNormRange_iff hkind t).2 ht

lemma primitive_sub_mem_reflectionNormRange_iff_sameParity
    (N : ReflectionLatticeNormalForm G s)
    (hkind : N.kind = .primitive)
    {t u : G.translationLattice.carrier}
    (ht : t ∈ reflectionFixedSubmodule G s)
    (hu : u ∈ reflectionFixedSubmodule G s) :
    t - u ∈ reflectionNormRange G s ↔
      Even (N.basis.repr t 0 - N.basis.repr u 0) := by
  rw [N.primitive_mem_reflectionNormRange_iff hkind]
  constructor
  · rintro ⟨-, heven⟩
    simpa using heven
  · intro heven
    constructor
    · exact (reflectionFixedSubmodule G s).sub_mem ht hu
    · simpa using heven

/-- Two primitive fixed vectors define the same norm-quotient class exactly when
their first coordinates have the same parity. -/
lemma primitive_fixed_vectors_sameClass_iff_sameParity
    (N : ReflectionLatticeNormalForm G s)
    (hkind : N.kind = .primitive)
    {t u : G.translationLattice.carrier}
    (ht : t ∈ reflectionFixedSubmodule G s)
    (hu : u ∈ reflectionFixedSubmodule G s) :
    (∃ v, v + G.latticeAction s v = t - u) ↔
      Even (N.basis.repr t 0 - N.basis.repr u 0) := by
  rw [← mem_reflectionNormRange_iff]
  exact N.primitive_sub_mem_reflectionNormRange_iff_sameParity hkind ht hu

lemma primitive_basis_zero_mem_fixed
    (N : ReflectionLatticeNormalForm G s)
    (_hkind : N.kind = .primitive) :
    N.basis 0 ∈ reflectionFixedSubmodule G s := by
  rw [mem_reflectionFixedSubmodule_iff,
    N.fixed_iff_second_coordinate_zero]
  simp

/-- The first basis vector represents the nonzero primitive norm class. -/
lemma primitive_basis_zero_not_mem_reflectionNormRange
    (N : ReflectionLatticeNormalForm G s)
    (hkind : N.kind = .primitive) :
    N.basis 0 ∉ reflectionNormRange G s := by
  rw [N.primitive_mem_reflectionNormRange_iff hkind]
  simp [N.primitive_basis_zero_mem_fixed hkind]

/-- Every primitive fixed vector belongs either to the zero norm class or to the
class represented by the first basis vector. -/
lemma primitive_fixed_zero_or_basis_zero_class
    (N : ReflectionLatticeNormalForm G s)
    (hkind : N.kind = .primitive)
    {t : G.translationLattice.carrier}
    (ht : t ∈ reflectionFixedSubmodule G s) :
    t ∈ reflectionNormRange G s ∨
      t - N.basis 0 ∈ reflectionNormRange G s := by
  rcases Int.even_or_odd (N.basis.repr t 0) with heven | hodd
  · left
    exact (N.primitive_mem_reflectionNormRange_iff hkind t).2 ⟨ht, heven⟩
  · right
    rw [N.primitive_sub_mem_reflectionNormRange_iff_sameParity hkind ht
      (N.primitive_basis_zero_mem_fixed hkind)]
    simpa using (even_sub_one.mpr hodd)

/-- Every nonzero primitive norm class is the class of the first basis vector. -/
lemma primitive_nonzero_class_eq_basis_zero_class
    (N : ReflectionLatticeNormalForm G s)
    (hkind : N.kind = .primitive)
    {t : G.translationLattice.carrier}
    (ht : t ∈ reflectionFixedSubmodule G s)
    (hnot : t ∉ reflectionNormRange G s) :
    t - N.basis 0 ∈ reflectionNormRange G s := by
  rcases N.primitive_fixed_zero_or_basis_zero_class hkind ht with h | h
  · exact (hnot h).elim
  · exact h

end ReflectionLatticeNormalForm

end PlaneGroup

end
end WallpaperGroups
