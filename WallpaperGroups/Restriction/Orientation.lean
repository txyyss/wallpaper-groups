import Mathlib.Analysis.Complex.Isometry
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.RingTheory.IntegralDomain
import WallpaperGroups.Basic.PlaneGroup

set_option linter.style.header false

/-!
# Orientation structure of plane point groups

This module defines the orientation-preserving subgroup of a plane point group and proves that it
is cyclic.  It also proves that every orientation-reversing element is an involution and conjugates
each orientation-preserving element to its inverse.  These results give a cyclic-or-dihedral
normal form without imposing any crystallographic order restriction.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion
open scoped RealInnerProductSpace

noncomputable section

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨Plane.finrank⟩

/-- The canonical orientation associated to the canonical coordinate basis of the plane. -/
def planeOrientation : Orientation ℝ Plane (Fin 2) :=
  Plane.canonicalRealBasis.orientation

/-- Forget that a plane linear equivalence is isometric, as a multiplicative map. -/
def linearIsometryToLinearEquiv :
    (Plane ≃ₗᵢ[ℝ] Plane) →* (Plane ≃ₗ[ℝ] Plane) where
  toFun h := h.toLinearEquiv
  map_one' := rfl
  map_mul' h k := by
    rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.toLinearEquiv_trans]
    rfl

/-- The determinant homomorphism on the point group of a plane group. -/
def pointGroupDet (G : PlaneGroup) : pointGroup G.carrier →* ℝˣ :=
  LinearEquiv.det.comp
    (linearIsometryToLinearEquiv.comp (pointGroup G.carrier).subtype)

/-- Evaluating `pointGroupDet` gives the determinant of the underlying real-linear map. -/
@[simp]
lemma pointGroupDet_apply (G : PlaneGroup) (h : pointGroup G.carrier) :
    ((pointGroupDet G h : ℝˣ) : ℝ) = LinearMap.det
      ((h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) := by
  simp [pointGroupDet, linearIsometryToLinearEquiv]

/-- The positive-determinant subgroup of a plane point group. -/
def orientationPreservingPointGroup (G : PlaneGroup) : Subgroup (pointGroup G.carrier) where
  carrier := {h | 0 < ((pointGroupDet G h : ℝˣ) : ℝ)}
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, Units.val_one]
    positivity
  mul_mem' := by
    intro h k hh hk
    simp only [Set.mem_setOf_eq] at hh hk ⊢
    change 0 < ((pointGroupDet G (h * k) : ℝˣ) : ℝ)
    rw [map_mul]
    exact mul_pos hh hk
  inv_mem' := by
    intro h hh
    simp only [Set.mem_setOf_eq] at hh ⊢
    change 0 < ((pointGroupDet G h⁻¹ : ℝˣ) : ℝ)
    rw [map_inv]
    simpa only [Units.val_inv_eq_inv_val] using inv_pos.mpr hh

/-- The first canonical coordinate vector is a unit vector. -/
lemma canonicalUnit_norm : ‖Plane.canonicalRealBasis 0‖ = 1 := by
  simp [Plane.canonicalRealBasis_apply]

/-- The first canonical coordinate vector is nonzero. -/
lemma canonicalUnit_ne_zero : Plane.canonicalRealBasis 0 ≠ 0 := by
  intro h
  simpa [h] using canonicalUnit_norm

/-- The canonical oriented unit vector identifies the plane isometrically with `ℂ`. -/
def planeToComplexLinearIsometry : Plane →ₗᵢ[ℝ] ℂ where
  toLinearMap := planeOrientation.kahler (Plane.canonicalRealBasis 0)
  norm_map' x := by
    rw [planeOrientation.norm_kahler]
    simp

/-- A fixed linear-isometric identification of the real plane with the complex plane. -/
def planeToComplex : Plane ≃ₗᵢ[ℝ] ℂ :=
  LinearIsometryEquiv.ofSurjective planeToComplexLinearIsometry
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Complex.finrank_real_complex])).mp planeToComplexLinearIsometry.injective)

/-- Conjugate plane linear isometries through the fixed complex identification. -/
def conjugateToComplex : (Plane ≃ₗᵢ[ℝ] Plane) ≃* (ℂ ≃ₗᵢ[ℝ] ℂ) where
  toFun f := (planeToComplex.symm.trans f).trans planeToComplex
  invFun f := (planeToComplex.trans f).trans planeToComplex.symm
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp
  map_mul' f g := by
    ext x
    simp

/-- Conjugating through `planeToComplex` preserves the real determinant. -/
@[simp]
lemma det_conjugateToComplex (f : Plane ≃ₗᵢ[ℝ] Plane) :
    LinearMap.det ((conjugateToComplex f).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
      LinearMap.det (f.toLinearEquiv : Plane →ₗ[ℝ] Plane) := by
  change LinearMap.det
      (((planeToComplex.toLinearEquiv.symm.trans f.toLinearEquiv).trans
        planeToComplex.toLinearEquiv : ℂ ≃ₗ[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = _
  simpa only [LinearEquiv.coe_det] using congrArg Units.val
    (LinearEquiv.det_conj f.toLinearEquiv planeToComplex.toLinearEquiv)

/-- Complex conjugation followed by a rotation is an involution. -/
lemma complex_conj_rotation_sq (a : Circle) :
    (Complex.conjLIE.trans (_root_.rotation a)) ^ 2 = 1 := by
  apply LinearIsometryEquiv.ext
  intro z
  change (a : ℂ) * (starRingEnd ℂ) ((a : ℂ) * (starRingEnd ℂ) z) = z
  rw [map_mul]
  rw [← Circle.coe_inv_eq_conj]
  simp

/-- Every negative-determinant plane linear isometry is an involution. -/
lemma negative_isometry_sq
    (s : Plane ≃ₗᵢ[ℝ] Plane)
    (hs : LinearMap.det (s.toLinearEquiv : Plane →ₗ[ℝ] Plane) < 0) :
    s ^ 2 = 1 := by
  have hc : LinearMap.det
      ((conjugateToComplex s).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) < 0 := by
    simpa using hs
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex (conjugateToComplex s)
  · exfalso
    rw [ha, det_rotation] at hc
    norm_num at hc
  · apply conjugateToComplex.injective
    rw [map_pow, map_one, ha, complex_conj_rotation_sq]

/-- Membership in the orientation-preserving subgroup gives positive real determinant. -/
lemma orientationPreserving_det_pos (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) :
    0 < LinearMap.det
      ((h.1 : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) := by
  have hp : 0 < ((pointGroupDet G h.1 : ℝˣ) : ℝ) := by
    simpa [orientationPreservingPointGroup] using h.2
  simpa only [pointGroupDet_apply] using hp

/-- A positive-determinant plane isometry is determined by one nonzero vector. -/
lemma positive_isometry_eq_of_apply_eq
    {f g : Plane ≃ₗᵢ[ℝ] Plane}
    (hf : 0 < LinearMap.det (f.toLinearEquiv : Plane →ₗ[ℝ] Plane))
    (hg : 0 < LinearMap.det (g.toLinearEquiv : Plane →ₗ[ℝ] Plane))
    {x : Plane} (hx : x ≠ 0) (hfg : f x = g x) : f = g := by
  obtain ⟨θ, rfl⟩ := planeOrientation.exists_linearIsometryEquiv_eq_of_det_pos hf
  obtain ⟨φ, rfl⟩ := planeOrientation.exists_linearIsometryEquiv_eq_of_det_pos hg
  have hang : θ = φ := by
    have hangle := congrArg (fun y => planeOrientation.oangle x y) hfg
    simpa [planeOrientation.oangle_rotation_self_right hx] using hangle
  exact congrArg planeOrientation.rotation hang

/-- A positive-determinant plane isometry has determinant exactly `1`. -/
lemma positive_isometry_det_eq_one
    (f : Plane ≃ₗᵢ[ℝ] Plane)
    (hf : 0 < LinearMap.det (f.toLinearEquiv : Plane →ₗ[ℝ] Plane)) :
    LinearMap.det (f.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 := by
  obtain ⟨θ, rfl⟩ := planeOrientation.exists_linearIsometryEquiv_eq_of_det_pos hf
  exact planeOrientation.det_rotation θ

/-- The complex rotation parameter obtained from a fixed oriented unit vector. -/
def rotationParameter (G : PlaneGroup) : orientationPreservingPointGroup G →* ℂ where
  toFun h := planeOrientation.kahler (Plane.canonicalRealBasis 0)
    ((h.1 : Plane ≃ₗᵢ[ℝ] Plane) (Plane.canonicalRealBasis 0))
  map_one' := by
    simp
  map_mul' h k := by
    let a : Plane := Plane.canonicalRealBasis 0
    let fh : Plane ≃ₗᵢ[ℝ] Plane := (h.1 : Plane ≃ₗᵢ[ℝ] Plane)
    let fk : Plane ≃ₗᵢ[ℝ] Plane := (k.1 : Plane ≃ₗᵢ[ℝ] Plane)
    have hpres : planeOrientation.kahler (fh a) (fh (fk a)) =
        planeOrientation.kahler a (fk a) :=
      planeOrientation.kahler_comp_linearIsometryEquiv fh
        (orientationPreserving_det_pos G h) a (fk a)
    have hmul := planeOrientation.kahler_mul (fh a) a (fh (fk a))
    change planeOrientation.kahler a (fh (fk a)) =
      planeOrientation.kahler a (fh a) * planeOrientation.kahler a (fk a)
    calc
      planeOrientation.kahler a (fh (fk a)) =
          ‖fh a‖ ^ 2 * planeOrientation.kahler a (fh (fk a)) := by
            simp [fh, a]
      _ = planeOrientation.kahler a (fh a) *
          planeOrientation.kahler (fh a) (fh (fk a)) := hmul.symm
      _ = planeOrientation.kahler a (fh a) *
          planeOrientation.kahler a (fk a) := by rw [hpres]

/-- The complex rotation parameter is injective on the positive point subgroup. -/
lemma rotationParameter_injective (G : PlaneGroup) :
    Function.Injective (rotationParameter G) := by
  intro h k hhk
  apply Subtype.ext
  apply Subtype.ext
  apply positive_isometry_eq_of_apply_eq
      (orientationPreserving_det_pos G h)
      (orientationPreserving_det_pos G k)
      canonicalUnit_ne_zero
  let a : Plane := Plane.canonicalRealBasis 0
  have hz : planeOrientation.kahler a
      (((h.1 : Plane ≃ₗᵢ[ℝ] Plane) a) - ((k.1 : Plane ≃ₗᵢ[ℝ] Plane) a)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (by simpa [rotationParameter, a] using hhk)
  rcases planeOrientation.eq_zero_or_eq_zero_of_kahler_eq_zero hz with ha | ha
  · exact (canonicalUnit_ne_zero ha).elim
  · exact sub_eq_zero.mp ha

/-- The orientation-preserving point subgroup is cyclic. -/
theorem orientationPreserving_isCyclic (G : PlaneGroup) :
    IsCyclic (orientationPreservingPointGroup G) :=
  isCyclic_of_injective_ringHom (rotationParameter G) (rotationParameter_injective G)

/-- A negative-determinant isometry reverses the canonical quarter turn. -/
lemma negative_isometry_rightAngleRotation
    (s : Plane ≃ₗᵢ[ℝ] Plane)
    (hs : LinearMap.det (s.toLinearEquiv : Plane →ₗ[ℝ] Plane) < 0)
    (x : Plane) :
    s (planeOrientation.rightAngleRotation x) =
      -planeOrientation.rightAngleRotation (s x) := by
  have hmap : Orientation.map (Fin 2) s.toLinearEquiv planeOrientation =
      -planeOrientation := by
    exact (planeOrientation.map_eq_neg_iff_det_neg s.toLinearEquiv (by simp)).2 hs
  have h := planeOrientation.rightAngleRotation_map s (s x)
  rw [hmap] at h
  simpa using h.symm

/-- Every negative-determinant plane isometry conjugates every positive one to its inverse. -/
lemma negative_conjugates_positive_to_inverse
    (s r : Plane ≃ₗᵢ[ℝ] Plane)
    (hs : LinearMap.det (s.toLinearEquiv : Plane →ₗ[ℝ] Plane) < 0)
    (hr : 0 < LinearMap.det (r.toLinearEquiv : Plane →ₗ[ℝ] Plane)) :
    s * r * s⁻¹ = r⁻¹ := by
  obtain ⟨θ, rfl⟩ := planeOrientation.exists_linearIsometryEquiv_eq_of_det_pos hr
  apply LinearIsometryEquiv.ext
  intro x
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply,
    LinearIsometryEquiv.coe_inv]
  rw [planeOrientation.rotation_apply, map_add, map_smul, map_smul]
  rw [negative_isometry_rightAngleRotation s hs]
  rw [s.apply_symm_apply]
  rw [planeOrientation.rotation_symm_apply]
  simp [sub_eq_add_neg]

/-- A point-group element outside the positive subgroup has negative determinant. -/
lemma pointGroup_det_neg_of_not_mem_orientationPreserving
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G) :
    LinearMap.det ((s : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) < 0 := by
  have hnpos : ¬ 0 < LinearMap.det
      ((s : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) := by
    intro hpos
    apply hs
    change 0 < ((pointGroupDet G s : ℝˣ) : ℝ)
    simpa only [pointGroupDet_apply] using hpos
  have hne : LinearMap.det
      ((s : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  exact lt_of_le_of_ne (le_of_not_gt hnpos) hne

/-- A reversing point-group element conjugates every positive element to its inverse. -/
lemma pointGroup_reversing_conjugates_to_inverse
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G)
    (r : orientationPreservingPointGroup G) :
    s * r.1 * s⁻¹ = (r.1)⁻¹ := by
  apply Subtype.ext
  exact negative_conjugates_positive_to_inverse
    (s : Plane ≃ₗᵢ[ℝ] Plane) (r.1 : Plane ≃ₗᵢ[ℝ] Plane)
    (pointGroup_det_neg_of_not_mem_orientationPreserving G s hs)
    (orientationPreserving_det_pos G r)

/-- A reversing point-group element is an involution. -/
lemma pointGroup_reversing_sq
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G) :
    s ^ 2 = 1 := by
  apply Subtype.ext
  exact negative_isometry_sq (s : Plane ≃ₗᵢ[ℝ] Plane)
    (pointGroup_det_neg_of_not_mem_orientationPreserving G s hs)

/-- The two orientation cosets give rotation/reflection normal form. -/
lemma pointGroup_rotation_or_reflection_mul
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G)
    (g : pointGroup G.carrier) :
    g ∈ orientationPreservingPointGroup G ∨
      ∃ r : orientationPreservingPointGroup G, g = s * r.1 := by
  by_cases hg : g ∈ orientationPreservingPointGroup G
  · exact Or.inl hg
  · right
    let r0 : pointGroup G.carrier := s⁻¹ * g
    have hsneg := pointGroup_det_neg_of_not_mem_orientationPreserving G s hs
    have hgneg := pointGroup_det_neg_of_not_mem_orientationPreserving G g hg
    have hsneg' : ((pointGroupDet G s : ℝˣ) : ℝ) < 0 := by
      simpa only [pointGroupDet_apply] using hsneg
    have hgneg' : ((pointGroupDet G g : ℝˣ) : ℝ) < 0 := by
      simpa only [pointGroupDet_apply] using hgneg
    have hr : r0 ∈ orientationPreservingPointGroup G := by
      change 0 < ((pointGroupDet G r0 : ℝˣ) : ℝ)
      change 0 < ((pointGroupDet G (s⁻¹ * g) : ℝˣ) : ℝ)
      rw [map_mul, map_inv]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos_of_neg_of_neg (inv_neg''.mpr hsneg') hgneg'
    refine ⟨⟨r0, hr⟩, ?_⟩
    simp [r0]

/-- Generator-and-normal-form data expressing that a group is dihedral over a cyclic subgroup. -/
structure DihedralData (P : Type*) [Group P] where
  /-- The cyclic subgroup of rotations. -/
  rotations : Subgroup P
  /-- The rotations form a cyclic group, including the trivial case. -/
  rotations_cyclic : IsCyclic rotations
  /-- A selected element in the reversing orientation coset. -/
  reflection : P
  /-- The selected reflection is not a rotation. -/
  reflection_not_mem : reflection ∉ rotations
  /-- The selected reflection is an involution. -/
  reflection_sq : reflection ^ 2 = 1
  /-- Conjugation by the selected reflection inverts every rotation. -/
  reflection_conjugates : ∀ r : rotations,
    reflection * r.1 * reflection⁻¹ = (r.1)⁻¹
  /-- Every element is a rotation or the selected reflection times a rotation. -/
  normal_form : ∀ g : P,
    g ∈ rotations ∨ ∃ r : rotations, g = reflection * r.1

/-- A reversing point-group element supplies explicit dihedral generator-and-normal-form data. -/
def pointGroupDihedralData
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G) :
    DihedralData (pointGroup G.carrier) where
  rotations := orientationPreservingPointGroup G
  rotations_cyclic := orientationPreserving_isCyclic G
  reflection := s
  reflection_not_mem := hs
  reflection_sq := pointGroup_reversing_sq G s hs
  reflection_conjugates := pointGroup_reversing_conjugates_to_inverse G s hs
  normal_form := pointGroup_rotation_or_reflection_mul G s hs

/-- Choose a rotation generator which every reversing element conjugates to its inverse. -/
theorem exists_orientationGenerator (G : PlaneGroup) :
    ∃ ρ : orientationPreservingPointGroup G,
      (∀ r, r ∈ Subgroup.zpowers ρ) ∧
      ∀ s : pointGroup G.carrier,
        s ∉ orientationPreservingPointGroup G →
          s * ρ.1 * s⁻¹ = (ρ.1)⁻¹ := by
  letI : IsCyclic (orientationPreservingPointGroup G) :=
    orientationPreserving_isCyclic G
  obtain ⟨ρ, hρ⟩ := IsCyclic.exists_generator
    (α := orientationPreservingPointGroup G)
  exact ⟨ρ, hρ, fun s hs => pointGroup_reversing_conjugates_to_inverse G s hs ρ⟩

/-- If there is no reversing element, the entire point group is cyclic. -/
theorem pointGroup_isCyclic_of_all_orientationPreserving
    (G : PlaneGroup)
    (hG : ∀ s : pointGroup G.carrier, s ∈ orientationPreservingPointGroup G) :
    IsCyclic (pointGroup G.carrier) := by
  letI : IsCyclic (orientationPreservingPointGroup G) :=
    orientationPreserving_isCyclic G
  exact isCyclic_of_surjective (orientationPreservingPointGroup G).subtype
    (fun s => ⟨⟨s, hG s⟩, rfl⟩)

/-- Every plane point group is cyclic or has explicit dihedral generator-and-normal-form data. -/
theorem pointGroup_cyclic_or_dihedralData (G : PlaneGroup) :
    IsCyclic (pointGroup G.carrier) ∨
      Nonempty (DihedralData (pointGroup G.carrier)) := by
  classical
  by_cases hG : ∀ s : pointGroup G.carrier, s ∈ orientationPreservingPointGroup G
  · exact Or.inl (pointGroup_isCyclic_of_all_orientationPreserving G hG)
  · push Not at hG
    obtain ⟨s, hs⟩ := hG
    exact Or.inr ⟨pointGroupDihedralData G s hs⟩

end

end WallpaperGroups
