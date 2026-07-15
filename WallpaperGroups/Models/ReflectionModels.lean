import WallpaperGroups.Models.RotationModels
import Mathlib.Analysis.Complex.OperatorNorm

set_option linter.style.header false
set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-!
# Standard one-reflection models

This module constructs the primitive and centered rectangular reflection lattices and packages
`pm`, `pg`, and `cm` as transparent two-coset plane groups.  The reflection coset records a
shift representative `s`; its square is the lattice translation `s + ρ s`.
-/

/-- Reflection in the first coordinate axis, transported from complex conjugation. -/
def axisReflection : Plane ≃ₗᵢ[ℝ] Plane :=
  (coordinateIsometry.trans Complex.conjLIE).trans coordinateIsometry.symm

@[simp]
lemma coordinateIsometry_axisReflection (x : Plane) :
    coordinateIsometry (axisReflection x) =
      star (coordinateIsometry x) := by
  simp [axisReflection]

@[simp]
lemma axisReflection_sq : axisReflection * axisReflection = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  change axisReflection (axisReflection x) = x
  apply coordinateIsometry.injective
  rw [coordinateIsometry_axisReflection, coordinateIsometry_axisReflection]
  simp

@[simp]
lemma axisReflection_inv : axisReflection⁻¹ = axisReflection := by
  rw [inv_eq_iff_mul_eq_one]
  exact axisReflection_sq

@[simp]
lemma axisReflection_standard_basis_zero :
    axisReflection (RankTwoLattice.standardLattice.basis 0 : Plane) =
      (RankTwoLattice.standardLattice.basis 0 : Plane) := by
  apply coordinateIsometry.injective
  rw [coordinateIsometry_axisReflection]
  rw [coordinateIsometry_squareLattice_basis_zero]
  simp

@[simp]
lemma axisReflection_standard_basis_one :
    axisReflection (RankTwoLattice.standardLattice.basis 1 : Plane) =
      -(RankTwoLattice.standardLattice.basis 1 : Plane) := by
  apply coordinateIsometry.injective
  rw [coordinateIsometry_axisReflection]
  rw [coordinateIsometry_squareLattice_basis_one]
  rw [map_neg, coordinateIsometry_squareLattice_basis_one]
  simp

lemma axisReflection_ne_one : axisReflection ≠ 1 := by
  intro h
  have h1 := LinearIsometryEquiv.congr_fun h
    (RankTwoLattice.standardLattice.basis 1 : Plane)
  rw [axisReflection_standard_basis_one] at h1
  change -(RankTwoLattice.standardLattice.basis 1 : Plane) =
    (RankTwoLattice.standardLattice.basis 1 : Plane) at h1
  have hc := congrArg coordinateIsometry h1
  rw [map_neg, coordinateIsometry_squareLattice_basis_one] at hc
  have him := congrArg Complex.im hc
  norm_num at him

lemma axisReflection_order : orderOf axisReflection = 2 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 2)]
  constructor
  · exact axisReflection_sq
  · intro m hm hpos
    interval_cases m
    all_goals norm_num at hpos hm ⊢
    exact axisReflection_ne_one

/-- The coordinate-axis reflection reverses orientation. -/
lemma axisReflection_det :
    LinearMap.det
      (axisReflection.toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1 := by
  change LinearMap.det
      (((coordinateIsometry.toLinearEquiv.trans
        Complex.conjLIE.toLinearEquiv).trans
          coordinateIsometry.symm.toLinearEquiv : Plane ≃ₗ[ℝ] Plane) :
            Plane →ₗ[ℝ] Plane) = -1
  have h := congrArg Units.val
    (LinearEquiv.det_conj Complex.conjLIE.toLinearEquiv
      coordinateIsometry.symm.toLinearEquiv)
  convert h using 1 <;> simp

lemma axisReflection_mem_squareStabilizer :
    axisReflection ∈ latticeStabilizer RankTwoLattice.standardLattice := by
  apply mem_latticeStabilizer_of_basis
  · intro i
    fin_cases i
    · change axisReflection
          (RankTwoLattice.standardLattice.basis (0 : Fin 2) : Plane) ∈ _
      rw [axisReflection_standard_basis_zero]
      exact (RankTwoLattice.standardLattice.basis 0).property
    · change axisReflection
          (RankTwoLattice.standardLattice.basis (1 : Fin 2) : Plane) ∈ _
      rw [axisReflection_standard_basis_one]
      exact RankTwoLattice.standardLattice.carrier.neg_mem
        (RankTwoLattice.standardLattice.basis 1).property
  · intro i
    rw [axisReflection_inv]
    fin_cases i
    · change axisReflection
          (RankTwoLattice.standardLattice.basis (0 : Fin 2) : Plane) ∈ _
      rw [axisReflection_standard_basis_zero]
      exact (RankTwoLattice.standardLattice.basis 0).property
    · change axisReflection
          (RankTwoLattice.standardLattice.basis (1 : Fin 2) : Plane) ∈ _
      rw [axisReflection_standard_basis_one]
      exact RankTwoLattice.standardLattice.carrier.neg_mem
        (RankTwoLattice.standardLattice.basis 1).property

/-! ## A centered rectangular lattice -/

/-- The real-linear shear taking `(1,i)` to `(1,(1+i)/2)`. -/
def centeredShear : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := ((z.re + z.im / 2 : ℝ) : ℂ) +
    ((z.im / 2 : ℝ) : ℂ) * Complex.I
  invFun z := ((z.re - z.im : ℝ) : ℂ) +
    ((2 * z.im : ℝ) : ℂ) * Complex.I
  map_add' z w := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  map_smul' r z := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  left_inv z := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
      ring
  right_inv z := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

@[simp]
lemma centeredShear_one : centeredShear 1 = 1 := by
  apply Complex.ext <;> simp [centeredShear]

@[simp]
lemma centeredShear_I :
    centeredShear Complex.I = (1 + Complex.I) / 2 := by
  apply Complex.ext <;> simp [centeredShear]

/-- Change of coordinates from the square frame to the centered rectangular frame. -/
def centeredPlaneEquiv : Plane ≃ₗ[ℝ] Plane :=
  (coordinateIsometry.toLinearEquiv.trans centeredShear).trans
    coordinateIsometry.symm.toLinearEquiv

/-- The centered rectangular lattice with basis `(1,(1+i)/2)`. -/
def centeredLattice : RankTwoLattice Plane :=
  RankTwoLattice.standardLattice.map centeredPlaneEquiv

@[simp]
lemma coordinateIsometry_centered_basis_zero :
    coordinateIsometry (centeredLattice.basis 0 : Plane) = 1 := by
  rw [show (centeredLattice.basis 0 : Plane) =
      centeredPlaneEquiv
        (RankTwoLattice.standardLattice.basis 0 : Plane) by rfl]
  rw [standardLattice_basis_coe]
  unfold centeredPlaneEquiv
  change coordinateIsometry
      (coordinateIsometry.symm
        (centeredShear
          (coordinateIsometry (Plane.canonicalRealBasis 0)))) = 1
  rw [coordinateIsometry.apply_symm_apply, coordinateIsometry_basis_zero,
    centeredShear_one]

@[simp]
lemma coordinateIsometry_centered_basis_one :
    coordinateIsometry (centeredLattice.basis 1 : Plane) =
      (1 + Complex.I) / 2 := by
  rw [show (centeredLattice.basis 1 : Plane) =
      centeredPlaneEquiv
        (RankTwoLattice.standardLattice.basis 1 : Plane) by rfl]
  rw [standardLattice_basis_coe]
  unfold centeredPlaneEquiv
  change coordinateIsometry
      (coordinateIsometry.symm
        (centeredShear
          (coordinateIsometry (Plane.canonicalRealBasis 1)))) =
            (1 + Complex.I) / 2
  rw [coordinateIsometry.apply_symm_apply, coordinateIsometry_basis_one,
    centeredShear_I]

lemma axisReflection_centered_basis_zero :
    axisReflection (centeredLattice.basis 0 : Plane) =
      (centeredLattice.basis 0 : Plane) := by
  apply coordinateIsometry.injective
  rw [coordinateIsometry_axisReflection]
  rw [coordinateIsometry_centered_basis_zero]
  simp

lemma axisReflection_centered_basis_one :
    axisReflection (centeredLattice.basis 1 : Plane) =
      (centeredLattice.basis 0 : Plane) -
        (centeredLattice.basis 1 : Plane) := by
  apply coordinateIsometry.injective
  rw [coordinateIsometry_axisReflection, coordinateIsometry_centered_basis_one]
  rw [map_sub, coordinateIsometry_centered_basis_zero,
    coordinateIsometry_centered_basis_one]
  apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]

lemma axisReflection_mem_centeredStabilizer :
    axisReflection ∈ latticeStabilizer centeredLattice := by
  apply mem_latticeStabilizer_of_basis
  · intro i
    fin_cases i
    · change axisReflection (centeredLattice.basis (0 : Fin 2) : Plane) ∈ _
      rw [axisReflection_centered_basis_zero]
      exact (centeredLattice.basis 0).property
    · change axisReflection (centeredLattice.basis (1 : Fin 2) : Plane) ∈ _
      rw [axisReflection_centered_basis_one]
      exact centeredLattice.carrier.sub_mem
        (centeredLattice.basis 0).property (centeredLattice.basis 1).property
  · intro i
    rw [axisReflection_inv]
    fin_cases i
    · change axisReflection (centeredLattice.basis (0 : Fin 2) : Plane) ∈ _
      rw [axisReflection_centered_basis_zero]
      exact (centeredLattice.basis 0).property
    · change axisReflection (centeredLattice.basis (1 : Fin 2) : Plane) ∈ _
      rw [axisReflection_centered_basis_one]
      exact centeredLattice.carrier.sub_mem
        (centeredLattice.basis 0).property (centeredLattice.basis 1).property

/-! ## A transparent shifted reflection extension -/

/-- Motions in the identity point coset have translation in `L`; motions in the reflection
coset have translation in `s + L`.  The condition `s + R s ∈ L` is exactly closure of the
reflection coset under multiplication. -/
def shiftedReflectionCarrier
    (L : RankTwoLattice Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane)
    (hR : R ∈ latticeStabilizer L)
    (hR2 : R * R = 1)
    (hs : s + R s ∈ L.carrier) :
    Subgroup (EuclideanMotion Plane) where
  carrier := {g |
    (linearPart g = 1 ∧ translationPart g ∈ L.carrier) ∨
    (linearPart g = R ∧ translationPart g - s ∈ L.carrier)}
  one_mem' := by
    left
    exact ⟨linearPart_one, L.carrier.zero_mem⟩
  mul_mem' := by
    intro g h hg hh
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · left
      constructor
      · rw [linearPart_mul, hg.1, hh.1, mul_one]
      · rw [translationPart_mul, hg.1]
        simpa using L.carrier.add_mem hg.2 hh.2
    · right
      constructor
      · rw [linearPart_mul, hg.1, hh.1, one_mul]
      · rw [translationPart_mul, hg.1]
        have hm := L.carrier.add_mem hg.2 hh.2
        convert hm using 1
        all_goals simp
        all_goals abel
    · right
      constructor
      · rw [linearPart_mul, hg.1, hh.1, mul_one]
      · rw [translationPart_mul, hg.1]
        have hRh : R (translationPart h) ∈ L.carrier :=
          (hR (translationPart h)).mp hh.2
        have hm := L.carrier.add_mem hg.2 hRh
        convert hm using 1
        all_goals abel
    · left
      constructor
      · rw [linearPart_mul, hg.1, hh.1, hR2]
      · rw [translationPart_mul, hg.1]
        have hRdiff : R (translationPart h - s) ∈ L.carrier :=
          (hR (translationPart h - s)).mp hh.2
        have hm := L.carrier.add_mem hs (L.carrier.add_mem hg.2 hRdiff)
        convert hm using 1
        all_goals simp [map_sub]
        all_goals abel
  inv_mem' := by
    intro g hg
    have hRi : R⁻¹ = R := by
      rw [inv_eq_iff_mul_eq_one]
      exact hR2
    rcases hg with hg | hg
    · left
      constructor
      · rw [linearPart_inv, hg.1, inv_one]
      · rw [translationPart_inv, hg.1, inv_one]
        simpa using L.carrier.neg_mem hg.2
    · right
      constructor
      · rw [linearPart_inv, hg.1, hRi]
      · rw [translationPart_inv, hg.1, hRi]
        have hRdiff : R (translationPart g - s) ∈ L.carrier :=
          (hR (translationPart g - s)).mp hg.2
        have hm := L.carrier.add_mem (L.carrier.neg_mem hRdiff)
          (L.carrier.neg_mem hs)
        convert hm using 1
        all_goals simp [map_sub]
        all_goals abel

@[simp]
theorem mem_shiftedReflectionCarrier
    (L : RankTwoLattice Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane)
    (hR : R ∈ latticeStabilizer L)
    (hR2 : R * R = 1)
    (hs : s + R s ∈ L.carrier)
    (g : EuclideanMotion Plane) :
    g ∈ shiftedReflectionCarrier L R s hR hR2 hs ↔
      (linearPart g = 1 ∧ translationPart g ∈ L.carrier) ∨
      (linearPart g = R ∧ translationPart g - s ∈ L.carrier) :=
  Iff.rfl

theorem shiftedReflectionCarrier_translationVectors
    (L : RankTwoLattice Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane)
    (hR : R ∈ latticeStabilizer L)
    (hR2 : R * R = 1)
    (hs : s + R s ∈ L.carrier)
    (hRne : R ≠ 1) :
    translationVectors (shiftedReflectionCarrier L R s hR hR2 hs) =
      L.toAddSubgroup := by
  ext t
  rw [mem_translationVectors]
  rw [mem_shiftedReflectionCarrier]
  rw [linearPart_translation, translationPart_translation]
  change
    ((1 = 1 ∧ t ∈ L.carrier) ∨ (1 = R ∧ t - s ∈ L.carrier)) ↔
      t ∈ L.carrier
  constructor
  · rintro (⟨_, ht⟩ | ⟨hbad, _⟩)
    · exact ht
    · exact False.elim (hRne hbad.symm)
  · intro ht
    exact Or.inl ⟨rfl, ht⟩

theorem shiftedReflectionCarrier_pointGroup
    (L : RankTwoLattice Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane)
    (hR : R ∈ latticeStabilizer L)
    (hR2 : R * R = 1)
    (hs : s + R s ∈ L.carrier) :
    pointGroup (shiftedReflectionCarrier L R s hR hR2 hs) =
      Subgroup.zpowers R := by
  apply le_antisymm
  · intro A hA
    rw [mem_pointGroup_iff] at hA
    obtain ⟨g, rfl⟩ := hA
    rcases g.property with hg | hg
    · rw [hg.1]
      exact (Subgroup.zpowers R).one_mem
    · rw [hg.1]
      exact Subgroup.mem_zpowers R
  · apply Subgroup.zpowers_le.mpr
    rw [mem_pointGroup_iff]
    let g : EuclideanMotion Plane := translation s * pureLinear R
    refine ⟨⟨g, ?_⟩, ?_⟩
    · right
      constructor
      · change linearPart (translation s * pureLinear R) = R
        rw [linearPart_mul, linearPart_translation,
          linearPart_pureLinear, one_mul]
      · simp [g, translationPart_mul]
    · change linearPart (translation s * pureLinear R) = R
      rw [linearPart_mul, linearPart_translation,
        linearPart_pureLinear, one_mul]

/-- A finite shifted reflection extension is a plane group with exact lattice and point group. -/
def shiftedReflectionPlaneGroup
    (L : RankTwoLattice Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane)
    (hR : R ∈ latticeStabilizer L)
    (hR2 : R * R = 1)
    (hs : s + R s ∈ L.carrier)
    (hRne : R ≠ 1)
    (horder : orderOf R = 2) : PlaneGroup := by
  letI : Finite (Subgroup.zpowers R) :=
    Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers, horder]
      norm_num)
  let C := shiftedReflectionCarrier L R s hR hR2 hs
  have hpoint : pointGroup C = Subgroup.zpowers R :=
    shiftedReflectionCarrier_pointGroup L R s hR hR2 hs
  letI : Finite (pointGroup C) := hpoint.symm ▸ inferInstance
  exact
    { carrier := C
      translationLattice := L
      translationLattice_carrier := by
        rw [shiftedReflectionCarrier_translationVectors L R s hR hR2 hs hRne]
        rfl
      pointGroup_finite := inferInstance }

/-! ## The three one-reflection standard-model candidates -/

/-- Primitive mirror model. -/
def pmModel : PlaneGroup :=
  shiftedReflectionPlaneGroup RankTwoLattice.standardLattice axisReflection 0
    axisReflection_mem_squareStabilizer axisReflection_sq
    (by simp) axisReflection_ne_one axisReflection_order

/-- Centered mirror model. -/
def cmModel : PlaneGroup :=
  shiftedReflectionPlaneGroup centeredLattice axisReflection 0
    axisReflection_mem_centeredStabilizer axisReflection_sq
    (by simp) axisReflection_ne_one axisReflection_order

/-- The half-primitive translation used by the glide-reflection model. -/
def glideShift : Plane :=
  (1 / 2 : ℝ) •
    (RankTwoLattice.standardLattice.basis 0 : Plane)

lemma glideShift_norm_mem :
    glideShift + axisReflection glideShift ∈
      RankTwoLattice.standardLattice.carrier := by
  have hfix : axisReflection glideShift = glideShift := by
    change axisReflection ((1 / 2 : ℝ) •
      (RankTwoLattice.standardLattice.basis 0 : Plane)) =
        (1 / 2 : ℝ) •
          (RankTwoLattice.standardLattice.basis 0 : Plane)
    rw [map_smul, axisReflection_standard_basis_zero]
  rw [hfix]
  have heq : glideShift + glideShift =
      (RankTwoLattice.standardLattice.basis 0 : Plane) := by
    rw [glideShift, ← add_smul]
    norm_num
  rw [heq]
  exact (RankTwoLattice.standardLattice.basis 0).property

/-- Primitive glide model. -/
def pgModel : PlaneGroup :=
  shiftedReflectionPlaneGroup RankTwoLattice.standardLattice axisReflection glideShift
    axisReflection_mem_squareStabilizer axisReflection_sq glideShift_norm_mem
    axisReflection_ne_one axisReflection_order

@[simp]
theorem pmModel_translationLattice :
    pmModel.translationLattice = RankTwoLattice.standardLattice :=
  rfl

@[simp]
theorem cmModel_translationLattice :
    cmModel.translationLattice = centeredLattice :=
  rfl

@[simp]
theorem pgModel_translationLattice :
    pgModel.translationLattice = RankTwoLattice.standardLattice :=
  rfl

theorem pmModel_pointGroup :
    pointGroup pmModel.carrier = Subgroup.zpowers axisReflection := by
  unfold pmModel shiftedReflectionPlaneGroup
  exact shiftedReflectionCarrier_pointGroup
    RankTwoLattice.standardLattice axisReflection 0
    axisReflection_mem_squareStabilizer axisReflection_sq (by simp)

theorem cmModel_pointGroup :
    pointGroup cmModel.carrier = Subgroup.zpowers axisReflection := by
  unfold cmModel shiftedReflectionPlaneGroup
  exact shiftedReflectionCarrier_pointGroup centeredLattice axisReflection 0
    axisReflection_mem_centeredStabilizer axisReflection_sq (by simp)

theorem pgModel_pointGroup :
    pointGroup pgModel.carrier = Subgroup.zpowers axisReflection := by
  unfold pgModel shiftedReflectionPlaneGroup
  exact shiftedReflectionCarrier_pointGroup
    RankTwoLattice.standardLattice axisReflection glideShift
    axisReflection_mem_squareStabilizer axisReflection_sq glideShift_norm_mem

@[simp]
theorem pmModel_pointGroup_card :
    Nat.card (pointGroup pmModel.carrier) = 2 := by
  rw [pmModel_pointGroup, Nat.card_zpowers, axisReflection_order]

@[simp]
theorem cmModel_pointGroup_card :
    Nat.card (pointGroup cmModel.carrier) = 2 := by
  rw [cmModel_pointGroup, Nat.card_zpowers, axisReflection_order]

@[simp]
theorem pgModel_pointGroup_card :
    Nat.card (pointGroup pgModel.carrier) = 2 := by
  rw [pgModel_pointGroup, Nat.card_zpowers, axisReflection_order]

/-! ## Lift-square and reflection-norm calculations -/

/-- The canonical representative of the reflection coset with shift `s`. -/
def shiftedReflectionLift (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane) :
    EuclideanMotion Plane :=
  translation s * pureLinear R

@[simp]
lemma shiftedReflectionLift_linearPart (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane) :
    linearPart (shiftedReflectionLift R s) = R := by
  rw [shiftedReflectionLift, linearPart_mul, linearPart_translation,
    linearPart_pureLinear, one_mul]

@[simp]
lemma shiftedReflectionLift_translationPart
    (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane) :
    translationPart (shiftedReflectionLift R s) = s := by
  simp [shiftedReflectionLift, translationPart_mul]

lemma shiftedReflectionLift_sq
    (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane)
    (hR2 : R * R = 1) :
    (shiftedReflectionLift R s) ^ 2 = translation (s + R s) := by
  apply ext_parts
  · rw [pow_two, translationPart_mul, shiftedReflectionLift_translationPart,
      shiftedReflectionLift_linearPart, translationPart_translation]
  · rw [pow_two, linearPart_mul, shiftedReflectionLift_linearPart,
      hR2, linearPart_translation]

/-- The canonical reflection-coset representative belongs to its shifted two-coset carrier. -/
theorem shiftedReflectionLift_mem
    (L : RankTwoLattice Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (s : Plane)
    (hR : R ∈ latticeStabilizer L)
    (hR2 : R * R = 1)
    (hs : s + R s ∈ L.carrier) :
    shiftedReflectionLift R s ∈
      shiftedReflectionCarrier L R s hR hR2 hs := by
  rw [mem_shiftedReflectionCarrier]
  right
  rw [shiftedReflectionLift_linearPart, shiftedReflectionLift_translationPart]
  exact ⟨rfl, by simp⟩

lemma pmModel_lift_sq :
    (shiftedReflectionLift axisReflection 0) ^ 2 = 1 := by
  rw [shiftedReflectionLift_sq axisReflection 0 axisReflection_sq]
  simp

lemma cmModel_lift_sq :
    (shiftedReflectionLift axisReflection 0) ^ 2 = 1 :=
  pmModel_lift_sq

lemma pgModel_lift_sq :
    (shiftedReflectionLift axisReflection glideShift) ^ 2 =
      translation (RankTwoLattice.standardLattice.basis 0 : Plane) := by
  rw [shiftedReflectionLift_sq axisReflection glideShift axisReflection_sq]
  congr 1
  exact_mod_cast (show glideShift + axisReflection glideShift =
      (RankTwoLattice.standardLattice.basis 0 : Plane) by
    have hfix : axisReflection glideShift = glideShift := by
      change axisReflection ((1 / 2 : ℝ) •
        (RankTwoLattice.standardLattice.basis 0 : Plane)) =
          (1 / 2 : ℝ) •
            (RankTwoLattice.standardLattice.basis 0 : Plane)
      rw [map_smul, axisReflection_standard_basis_zero]
    rw [hfix, glideShift, ← add_smul]
    norm_num)


end
end WallpaperGroups
