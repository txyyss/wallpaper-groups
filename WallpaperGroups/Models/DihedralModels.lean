import WallpaperGroups.Models.ReflectionModels
import WallpaperGroups.Presentations.TwoReflectionExtension
import WallpaperGroups.Restriction.DihedralNormalForms
import Mathlib.GroupTheory.SpecificGroups.Dihedral

set_option linter.style.header false

/-!
# Transparent finite-coset models for dihedral wallpaper groups

A finite point group is represented faithfully on the plane.  A section of its affine cosets is
stored only modulo the selected lattice: its failure to be a genuine cocycle is required to be a
lattice vector.  This gives a single transparent normal form for both symmorphic and glide models.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace WallpaperGroups

open EuclideanMotion
open PlaneGroup

noncomputable section

/-- Data for a transparent plane group with a prescribed finite point group and a section whose
factor set takes values in the translation lattice. -/
structure FiniteCosetData (P : Type*) [Group P] [Finite P] where
  lattice : RankTwoLattice Plane
  linearRep : P →* (Plane ≃ₗᵢ[ℝ] Plane)
  linearRep_injective : Function.Injective linearRep
  preserves_lattice : ∀ p : P, linearRep p ∈ latticeStabilizer lattice
  shift : P → Plane
  shift_one_mem : shift 1 ∈ lattice.carrier
  cocycle_mem : ∀ p q : P,
    shift p + linearRep p (shift q) - shift (p * q) ∈ lattice.carrier

/-- The transparent affine-coset carrier attached to finite-coset data. -/
def finiteCosetCarrier {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) : Subgroup (EuclideanMotion Plane) where
  carrier := {g | ∃ p : P,
    linearPart g = D.linearRep p ∧
      translationPart g - D.shift p ∈ D.lattice.carrier}
  one_mem' := by
    refine ⟨1, ?_, ?_⟩
    · rw [linearPart_one, map_one]
    · rw [translationPart_one, zero_sub]
      exact D.lattice.carrier.neg_mem D.shift_one_mem
  mul_mem' := by
    intro g h hg hh
    obtain ⟨p, hpLinear, hpShift⟩ := hg
    obtain ⟨q, hqLinear, hqShift⟩ := hh
    refine ⟨p * q, ?_, ?_⟩
    · rw [linearPart_mul, hpLinear, hqLinear, map_mul]
    · rw [translationPart_mul, hpLinear]
      have hqMapped : D.linearRep p (translationPart h - D.shift q) ∈
          D.lattice.carrier :=
        (D.preserves_lattice p (translationPart h - D.shift q)).mp hqShift
      have hsum := D.lattice.carrier.add_mem
        (D.lattice.carrier.add_mem hpShift hqMapped) (D.cocycle_mem p q)
      convert hsum using 1
      simp only [map_sub]
      abel
  inv_mem' := by
    intro g hg
    obtain ⟨p, hpLinear, hpShift⟩ := hg
    refine ⟨p⁻¹, ?_, ?_⟩
    · rw [linearPart_inv, hpLinear, map_inv]
    · rw [translationPart_inv, hpLinear]
      have hbase : -(D.linearRep p)⁻¹ (translationPart g - D.shift p) ∈
          D.lattice.carrier := by
        simpa only [map_inv] using D.lattice.carrier.neg_mem
          ((D.preserves_lattice p⁻¹ (translationPart g - D.shift p)).mp hpShift)
      have hcocycle := D.cocycle_mem p⁻¹ p
      rw [map_inv] at hcocycle
      have hmem := D.lattice.carrier.sub_mem
        (D.lattice.carrier.sub_mem hbase hcocycle) D.shift_one_mem
      convert hmem using 1
      simp only [map_sub, inv_mul_cancel]
      abel

@[simp]
theorem mem_finiteCosetCarrier {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (g : EuclideanMotion Plane) :
    g ∈ finiteCosetCarrier D ↔
      ∃ p : P, linearPart g = D.linearRep p ∧
        translationPart g - D.shift p ∈ D.lattice.carrier :=
  Iff.rfl

/-- The pure translations in a finite-coset carrier are exactly the selected lattice. -/
theorem finiteCosetCarrier_translationVectors
    {P : Type*} [Group P] [Finite P] (D : FiniteCosetData P) :
    translationVectors (finiteCosetCarrier D) = D.lattice.toAddSubgroup := by
  ext t
  rw [mem_translationVectors, mem_finiteCosetCarrier,
    linearPart_translation, translationPart_translation]
  constructor
  · rintro ⟨p, hp, ht⟩
    have hpOne : p = 1 := by
      apply D.linearRep_injective
      simpa using hp.symm
    subst p
    change t ∈ D.lattice.carrier
    have hsum := D.lattice.carrier.add_mem ht D.shift_one_mem
    convert hsum using 1
    abel
  · intro ht
    refine ⟨1, by simp, ?_⟩
    exact D.lattice.carrier.sub_mem ht D.shift_one_mem

/-- The point group of a finite-coset carrier is the range of its faithful representation. -/
theorem finiteCosetCarrier_pointGroup
    {P : Type*} [Group P] [Finite P] (D : FiniteCosetData P) :
    pointGroup (finiteCosetCarrier D) = D.linearRep.range := by
  ext A
  constructor
  · rw [mem_pointGroup_iff]
    rintro ⟨g, rfl⟩
    obtain ⟨p, hp, -⟩ := g.property
    exact ⟨p, hp.symm⟩
  · rintro ⟨p, rfl⟩
    rw [mem_pointGroup_iff]
    let g : EuclideanMotion Plane := translation (D.shift p) * pureLinear (D.linearRep p)
    refine ⟨⟨g, ?_⟩, ?_⟩
    · rw [mem_finiteCosetCarrier]
      refine ⟨p, ?_, ?_⟩
      · simp only [g, linearPart_mul, linearPart_translation,
          linearPart_pureLinear, one_mul]
      · simp [g, translationPart_mul]
    · simp only [g, linearPart_mul, linearPart_translation,
        linearPart_pureLinear, one_mul]

/-- A faithful finite-coset datum determines a plane group with exact lattice and point group. -/
def finiteCosetPlaneGroup {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) : PlaneGroup := by
  letI : Finite D.linearRep.range :=
    Finite.of_surjective D.linearRep.rangeRestrict D.linearRep.rangeRestrict_surjective
  letI : Finite (pointGroup (finiteCosetCarrier D)) :=
    finiteCosetCarrier_pointGroup D ▸ inferInstance
  exact
    { carrier := finiteCosetCarrier D
      translationLattice := D.lattice
      translationLattice_carrier := by
        rw [finiteCosetCarrier_translationVectors]
        rfl
      pointGroup_finite := inferInstance }

@[simp]
theorem finiteCosetPlaneGroup_translationLattice
    {P : Type*} [Group P] [Finite P] (D : FiniteCosetData P) :
    (finiteCosetPlaneGroup D).translationLattice = D.lattice :=
  rfl

theorem finiteCosetPlaneGroup_pointGroup
    {P : Type*} [Group P] [Finite P] (D : FiniteCosetData P) :
    pointGroup (finiteCosetPlaneGroup D).carrier = D.linearRep.range := by
  exact finiteCosetCarrier_pointGroup D

@[simp]
theorem finiteCosetPlaneGroup_pointGroup_card
    {P : Type*} [Group P] [Finite P] (D : FiniteCosetData P) :
    Nat.card (pointGroup (finiteCosetPlaneGroup D).carrier) = Nat.card P := by
  rw [finiteCosetPlaneGroup_pointGroup]
  let e : P ≃ D.linearRep.range :=
    Equiv.ofBijective D.linearRep.rangeRestrict ⟨by
      intro x y h
      apply D.linearRep_injective
      exact congrArg Subtype.val h
    , D.linearRep.rangeRestrict_surjective⟩
  exact Nat.card_congr e.symm

/-! ## Canonical point elements and affine representatives -/

/-- The point-group element represented by a finite-coset coordinate. -/
def finiteCosetPointElement {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) :
    pointGroup (finiteCosetPlaneGroup D).carrier :=
  ⟨D.linearRep p, by
    rw [finiteCosetPlaneGroup_pointGroup D]
    exact ⟨p, rfl⟩⟩

@[simp]
theorem finiteCosetPointElement_coe {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) :
    (finiteCosetPointElement D p : Plane ≃ₗᵢ[ℝ] Plane) = D.linearRep p :=
  rfl

@[simp]
theorem finiteCosetPointElement_one {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) : finiteCosetPointElement D 1 = 1 := by
  apply Subtype.ext
  simp

@[simp]
theorem finiteCosetPointElement_mul {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p q : P) :
    finiteCosetPointElement D (p * q) =
      finiteCosetPointElement D p * finiteCosetPointElement D q := by
  apply Subtype.ext
  simp

@[simp]
theorem finiteCosetPointElement_inv {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) :
    finiteCosetPointElement D p⁻¹ = (finiteCosetPointElement D p)⁻¹ := by
  apply Subtype.ext
  simp

/-- The chosen affine representative of a finite-coset coordinate. -/
def finiteCosetRepresentative {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) : EuclideanMotion Plane :=
  translation (D.shift p) * pureLinear (D.linearRep p)

theorem finiteCosetRepresentative_mem {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) :
    finiteCosetRepresentative D p ∈ (finiteCosetPlaneGroup D).carrier := by
  change finiteCosetRepresentative D p ∈ finiteCosetCarrier D
  rw [mem_finiteCosetCarrier]
  refine ⟨p, ?_, ?_⟩
  · simp only [finiteCosetRepresentative, linearPart_mul,
      linearPart_translation, linearPart_pureLinear, one_mul]
  · simp [finiteCosetRepresentative, translationPart_mul]

/-- The chosen affine representative, bundled as an element of the model. -/
def finiteCosetLift {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) : (finiteCosetPlaneGroup D).carrier :=
  ⟨finiteCosetRepresentative D p, finiteCosetRepresentative_mem D p⟩

@[simp]
theorem finiteCosetLift_coe {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) :
    (finiteCosetLift D p : EuclideanMotion Plane) = finiteCosetRepresentative D p :=
  rfl

@[simp]
theorem finiteCosetLift_projection {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) :
    pointProjection (finiteCosetPlaneGroup D).carrier (finiteCosetLift D p) =
      finiteCosetPointElement D p := by
  apply Subtype.ext
  change linearPart (finiteCosetRepresentative D p) = D.linearRep p
  simp only [finiteCosetRepresentative, linearPart_mul,
    linearPart_translation, linearPart_pureLinear, one_mul]

/-! ## Faithful linear dihedral representations -/

/-- Integer powers of a circle element as an additive homomorphism into the additive type tag. -/
def circleZPowAddHom (a : Circle) : ℤ →+ Additive Circle where
  toFun k := Additive.ofMul (a ^ k)
  map_zero' := by simp
  map_add' m n := by
    change a ^ (m + n) = a ^ m * a ^ n
    exact zpow_add a m n

/-- Powers of an element of order dividing `q`, indexed by `ZMod q`. -/
def circlePowerMod (a : Circle) (q : ℕ) (hq : a ^ q = 1) : ZMod q →+ Additive Circle :=
  ZMod.lift q ⟨circleZPowAddHom a, by
    change a ^ (q : ℤ) = 1
    simpa using hq⟩

@[simp]
theorem circlePowerMod_coe (a : Circle) (q : ℕ) (hq : a ^ q = 1) (k : ℤ) :
    Additive.toMul (circlePowerMod a q hq (k : ZMod q)) = a ^ k := by
  simp [circlePowerMod, circleZPowAddHom]

@[simp]
theorem circlePowerMod_zero (a : Circle) (q : ℕ) (hq : a ^ q = 1) :
    Additive.toMul (circlePowerMod a q hq 0) = 1 := by
  change Additive.toMul (circlePowerMod a q hq 0) = Additive.toMul 0
  rw [map_zero]

@[simp]
theorem circlePowerMod_add (a : Circle) (q : ℕ) (hq : a ^ q = 1)
    (i j : ZMod q) :
    Additive.toMul (circlePowerMod a q hq (i + j)) =
      Additive.toMul (circlePowerMod a q hq i) *
        Additive.toMul (circlePowerMod a q hq j) := by
  change Additive.toMul (circlePowerMod a q hq (i + j)) =
    Additive.toMul (circlePowerMod a q hq i + circlePowerMod a q hq j)
  rw [map_add]

@[simp]
theorem circlePowerMod_neg (a : Circle) (q : ℕ) (hq : a ^ q = 1)
    (i : ZMod q) :
    Additive.toMul (circlePowerMod a q hq (-i)) =
      (Additive.toMul (circlePowerMod a q hq i))⁻¹ := by
  change Additive.toMul (circlePowerMod a q hq (-i)) =
    Additive.toMul (-(circlePowerMod a q hq i))
  rw [map_neg]

theorem circlePowerMod_injective (a : Circle) (q : ℕ)
    (horder : orderOf a = q) :
    Function.Injective (circlePowerMod a q (by rw [← horder]; exact pow_orderOf_eq_one a)) := by
  unfold circlePowerMod
  rw [ZMod.lift_injective]
  intro m hm
  change a ^ m = 1 at hm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hd : (orderOf a : ℤ) ∣ m :=
    (orderOf_dvd_iff_zpow_eq_one).2 hm
  simpa [horder] using hd

/-- Reflection across the coordinate axis conjugates every plane rotation to its inverse. -/
theorem axisReflection_mul_planeRotation (a : Circle) :
    axisReflection * planeRotation a = planeRotation a⁻¹ * axisReflection := by
  apply LinearIsometryEquiv.ext
  intro x
  apply coordinateIsometry.injective
  change coordinateIsometry (axisReflection (planeRotation a x)) =
    coordinateIsometry (planeRotation a⁻¹ (axisReflection x))
  rw [coordinateIsometry_axisReflection, coordinateIsometry_planeRotation,
    coordinateIsometry_planeRotation, coordinateIsometry_axisReflection]
  rw [star_mul']
  have ha : star (a : ℂ) = ((a⁻¹ : Circle) : ℂ) := by
    rw [← starRingEnd_apply, ← Circle.coe_inv_eq_conj]
  rw [ha]

/-- Plane rotations commute. -/
theorem planeRotation_commute (a b : Circle) :
    planeRotation a * planeRotation b = planeRotation b * planeRotation a := by
  rw [← planeRotation_mul, ← planeRotation_mul, mul_comm]

/-- The equivalent relation with the reflection on the right. -/
theorem planeRotation_mul_axisReflection (a : Circle) :
    planeRotation a * axisReflection = axisReflection * planeRotation a⁻¹ := by
  simpa using (axisReflection_mul_planeRotation a⁻¹).symm

/-- The faithful dihedral representation with `r i` acting by a rotation and `sr i` by the
selected axis reflection followed by that rotation. -/
def dihedralLinearRepresentation (a : Circle) (q : ℕ) (horder : orderOf a = q) :
    DihedralGroup q →* (Plane ≃ₗᵢ[ℝ] Plane) where
  toFun
    | .r i => planeRotation
        (Additive.toMul (circlePowerMod a q (by rw [← horder]; exact pow_orderOf_eq_one a) i))
    | .sr i => axisReflection * planeRotation
        (Additive.toMul (circlePowerMod a q (by rw [← horder]; exact pow_orderOf_eq_one a) i))
  map_one' := by
    rw [DihedralGroup.one_def]
    simp
  map_mul' x y := by
    let hq : a ^ q = 1 := by rw [← horder]; exact pow_orderOf_eq_one a
    cases x with
    | r i =>
        cases y with
        | r j =>
            simp only [DihedralGroup.r_mul_r, circlePowerMod_add, planeRotation_mul]
        | sr j =>
            simp only [DihedralGroup.r_mul_sr]
            rw [show j - i = j + -i by abel, circlePowerMod_add,
              circlePowerMod_neg, planeRotation_mul]
            calc
              axisReflection * planeRotation
                    (Additive.toMul (circlePowerMod a q hq j)) *
                  planeRotation
                    (Additive.toMul (circlePowerMod a q hq i))⁻¹ =
                  axisReflection *
                    (planeRotation (Additive.toMul (circlePowerMod a q hq j)) *
                      planeRotation
                        (Additive.toMul (circlePowerMod a q hq i))⁻¹) := by
                    rw [mul_assoc]
              _ = axisReflection *
                    (planeRotation
                        (Additive.toMul (circlePowerMod a q hq i))⁻¹ *
                      planeRotation
                        (Additive.toMul (circlePowerMod a q hq j))) := by
                    rw [planeRotation_commute]
              _ = (axisReflection * planeRotation
                    (Additive.toMul (circlePowerMod a q hq i))⁻¹) *
                  planeRotation
                    (Additive.toMul (circlePowerMod a q hq j)) := by
                    rw [mul_assoc]
              _ = (planeRotation (Additive.toMul (circlePowerMod a q hq i)) *
                    axisReflection) *
                  planeRotation
                    (Additive.toMul (circlePowerMod a q hq j)) := by
                    rw [planeRotation_mul_axisReflection]
              _ = planeRotation (Additive.toMul (circlePowerMod a q hq i)) *
                  (axisReflection * planeRotation
                    (Additive.toMul (circlePowerMod a q hq j))) := by
                    rw [mul_assoc]
    | sr i =>
        cases y with
        | r j =>
            simp only [DihedralGroup.sr_mul_r, circlePowerMod_add,
              planeRotation_mul]
            exact (mul_assoc _ _ _).symm
        | sr j =>
            simp only [DihedralGroup.sr_mul_sr]
            rw [show j - i = j + -i by abel, circlePowerMod_add,
              circlePowerMod_neg, planeRotation_mul]
            calc
              planeRotation (Additive.toMul (circlePowerMod a q hq j)) *
                    planeRotation
                      (Additive.toMul (circlePowerMod a q hq i))⁻¹ =
                  planeRotation
                      (Additive.toMul (circlePowerMod a q hq i))⁻¹ *
                    planeRotation
                      (Additive.toMul (circlePowerMod a q hq j)) := by
                  rw [planeRotation_commute]
              _ = axisReflection *
                    (axisReflection * planeRotation
                      (Additive.toMul (circlePowerMod a q hq i))⁻¹) *
                    planeRotation
                      (Additive.toMul (circlePowerMod a q hq j)) := by
                  rw [← mul_assoc, axisReflection_sq, one_mul]
              _ = axisReflection *
                    (planeRotation (Additive.toMul (circlePowerMod a q hq i)) *
                      axisReflection) *
                    planeRotation
                      (Additive.toMul (circlePowerMod a q hq j)) := by
                  rw [planeRotation_mul_axisReflection]
              _ = (axisReflection * planeRotation
                    (Additive.toMul (circlePowerMod a q hq i))) *
                  (axisReflection * planeRotation
                    (Additive.toMul (circlePowerMod a q hq j))) := by group

/-- A reflection followed by a rotation has determinant `-1`. -/
theorem axisReflection_mul_planeRotation_det (a : Circle) :
    LinearMap.det
      (((axisReflection * planeRotation a).toLinearEquiv : Plane →ₗ[ℝ] Plane)) = -1 := by
  change LinearMap.det
    (axisReflection.toLinearEquiv.toLinearMap.comp
      (planeRotation a).toLinearEquiv.toLinearMap) = -1
  rw [LinearMap.det_comp, axisReflection_det, planeRotation_det]
  norm_num

/-- A rotation cannot equal a reflection followed by a rotation. -/
theorem planeRotation_ne_axisReflection_mul_planeRotation (a b : Circle) :
    planeRotation a ≠ axisReflection * planeRotation b := by
  intro h
  have hdet := congrArg
    (fun A : Plane ≃ₗᵢ[ℝ] Plane =>
      LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)) h
  rw [planeRotation_det, axisReflection_mul_planeRotation_det] at hdet
  norm_num at hdet

/-- The standard linear dihedral representation is faithful when the rotation has exact order
`q`. -/
theorem dihedralLinearRepresentation_injective
    (a : Circle) (q : ℕ) (horder : orderOf a = q) :
    Function.Injective (dihedralLinearRepresentation a q horder) := by
  intro x y hxy
  cases x with
  | r i =>
      cases y with
      | r j =>
          apply congrArg DihedralGroup.r
          apply circlePowerMod_injective a q horder
          apply planeRotationHom_injective
          change planeRotation
              (Additive.toMul (circlePowerMod a q _ i)) =
            planeRotation
              (Additive.toMul (circlePowerMod a q _ j)) at hxy
          exact hxy
      | sr j =>
          exfalso
          change planeRotation
              (Additive.toMul (circlePowerMod a q _ i)) =
            axisReflection * planeRotation
              (Additive.toMul (circlePowerMod a q _ j)) at hxy
          exact (planeRotation_ne_axisReflection_mul_planeRotation _ _ hxy).elim
  | sr i =>
      cases y with
      | r j =>
          exfalso
          change axisReflection * planeRotation
              (Additive.toMul (circlePowerMod a q _ i)) =
            planeRotation
              (Additive.toMul (circlePowerMod a q _ j)) at hxy
          exact (planeRotation_ne_axisReflection_mul_planeRotation _ _ hxy.symm).elim
      | sr j =>
          apply congrArg DihedralGroup.sr
          apply circlePowerMod_injective a q horder
          apply planeRotationHom_injective
          apply mul_left_cancel (a := axisReflection)
          change axisReflection * planeRotation
              (Additive.toMul (circlePowerMod a q _ i)) =
            axisReflection * planeRotation
              (Additive.toMul (circlePowerMod a q _ j)) at hxy
          exact hxy

/-- Every element of the displayed dihedral representation preserves a lattice when its rotation
and reflection generators do. -/
theorem dihedralLinearRepresentation_mem_stabilizer
    (L : RankTwoLattice Plane) (a : Circle) (q : ℕ) (horder : orderOf a = q)
    (ha : planeRotation a ∈ latticeStabilizer L)
    (hs : axisReflection ∈ latticeStabilizer L)
    (p : DihedralGroup q) :
    dihedralLinearRepresentation a q horder p ∈ latticeStabilizer L := by
  cases p with
  | r i =>
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
      rw [show dihedralLinearRepresentation a q horder (.r (k : ZMod q)) =
        planeRotation (a ^ k) by simp [dihedralLinearRepresentation]]
      change planeRotationHom (a ^ k) ∈ latticeStabilizer L
      rw [map_zpow]
      exact (latticeStabilizer L).zpow_mem ha k
  | sr i =>
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
      rw [show dihedralLinearRepresentation a q horder (.sr (k : ZMod q)) =
        axisReflection * planeRotation (a ^ k) by
          simp [dihedralLinearRepresentation]]
      apply (latticeStabilizer L).mul_mem hs
      change planeRotationHom (a ^ k) ∈ latticeStabilizer L
      rw [map_zpow]
      exact (latticeStabilizer L).zpow_mem ha k

/-- Symmorphic finite-coset data for a faithful dihedral lattice action. -/
def symmorphicDihedralCosetData
    (L : RankTwoLattice Plane) (a : Circle) (q : ℕ) [NeZero q]
    (horder : orderOf a = q)
    (ha : planeRotation a ∈ latticeStabilizer L)
    (hs : axisReflection ∈ latticeStabilizer L) :
    FiniteCosetData (DihedralGroup q) where
  lattice := L
  linearRep := dihedralLinearRepresentation a q horder
  linearRep_injective := dihedralLinearRepresentation_injective a q horder
  preserves_lattice := dihedralLinearRepresentation_mem_stabilizer L a q horder ha hs
  shift := fun _ => 0
  shift_one_mem := L.carrier.zero_mem
  cocycle_mem := by simp

/-- Common symmorphic dihedral model. -/
def symmorphicDihedralModel
    (L : RankTwoLattice Plane) (a : Circle) (q : ℕ) [NeZero q]
    (horder : orderOf a = q)
    (ha : planeRotation a ∈ latticeStabilizer L)
    (hs : axisReflection ∈ latticeStabilizer L) : PlaneGroup :=
  finiteCosetPlaneGroup (symmorphicDihedralCosetData L a q horder ha hs)

/-- The half turn sends every plane vector to its negative. -/
@[simp]
theorem halfTurn_apply (x : Plane) :
    planeRotation (squareRoot ^ 2) x = -x := by
  apply coordinateIsometry.injective
  rw [coordinateIsometry_planeRotation, map_neg]
  rw [show ((squareRoot ^ 2 : Circle) : ℂ) = -1 by
    simpa using congrArg (fun z : Circle => (z : ℂ)) squareRoot_sq]
  ring

/-- The half turn preserves every rank-two lattice. -/
theorem halfTurn_mem_stabilizer (L : RankTwoLattice Plane) :
    planeRotation (squareRoot ^ 2) ∈ latticeStabilizer L := by
  apply mem_latticeStabilizer_of_basis
  · intro i
    rw [halfTurn_apply]
    exact L.carrier.neg_mem (L.basis i).property
  · intro i
    have hinv : (planeRotation (squareRoot ^ 2))⁻¹ =
        planeRotation (squareRoot ^ 2) := by
      rw [planeRotation_inv]
      apply congrArg planeRotation
      rw [show squareRoot ^ 2 = (-1 : Circle) from squareRoot_sq]
      simp
    rw [hinv, halfTurn_apply]
    exact L.carrier.neg_mem (L.basis i).property

/-- Coordinate-axis reflection preserves the triangular lattice. -/
theorem axisReflection_mem_hexStabilizer :
    axisReflection ∈ latticeStabilizer hexLattice := by
  have hzero : axisReflection (hexLattice.basis 0 : Plane) =
      (hexLattice.basis 0 : Plane) := by
    apply coordinateIsometry.injective
    simp
  have hone : axisReflection (hexLattice.basis 1 : Plane) =
      (hexLattice.basis 0 : Plane) - (hexLattice.basis 1 : Plane) := by
    apply coordinateIsometry.injective
    rw [coordinateIsometry_axisReflection, coordinateIsometry_hexLattice_basis_one,
      map_sub, coordinateIsometry_hexLattice_basis_zero,
      coordinateIsometry_hexLattice_basis_one]
    apply Complex.ext
    all_goals simp [hexRoot]
    all_goals ring
  apply mem_latticeStabilizer_of_basis
  · intro i
    fin_cases i
    · change axisReflection (hexLattice.basis (0 : Fin 2) : Plane) ∈
        hexLattice.carrier
      rw [hzero]
      exact (hexLattice.basis 0).property
    · change axisReflection (hexLattice.basis (1 : Fin 2) : Plane) ∈
        hexLattice.carrier
      rw [hone]
      exact hexLattice.carrier.sub_mem
        (hexLattice.basis 0).property (hexLattice.basis 1).property
  · intro i
    rw [axisReflection_inv]
    fin_cases i
    · change axisReflection (hexLattice.basis (0 : Fin 2) : Plane) ∈
        hexLattice.carrier
      rw [hzero]
      exact (hexLattice.basis 0).property
    · change axisReflection (hexLattice.basis (1 : Fin 2) : Plane) ∈
        hexLattice.carrier
      rw [hone]
      exact hexLattice.carrier.sub_mem
        (hexLattice.basis 0).property (hexLattice.basis 1).property

/-! ## The second order-three reflection embedding -/

/-- The half turn is an involution. -/
@[simp]
theorem halfTurn_sq :
    planeRotation (squareRoot ^ 2) * planeRotation (squareRoot ^ 2) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  simp

theorem halfTurn_commute_axisReflection :
    planeRotation (squareRoot ^ 2) * axisReflection =
      axisReflection * planeRotation (squareRoot ^ 2) := by
  apply LinearIsometryEquiv.ext
  intro x
  simp

theorem halfTurn_commute_dihedralLinearRepresentation
    (a : Circle) (q : ℕ) (horder : orderOf a = q) (p : DihedralGroup q) :
    planeRotation (squareRoot ^ 2) * dihedralLinearRepresentation a q horder p =
      dihedralLinearRepresentation a q horder p * planeRotation (squareRoot ^ 2) := by
  cases p with
  | r i =>
      apply planeRotation_commute
  | sr i =>
      simp only [dihedralLinearRepresentation]
      calc
        planeRotation (squareRoot ^ 2) *
              (axisReflection * planeRotation
                (Additive.toMul (circlePowerMod a q _ i))) =
            (planeRotation (squareRoot ^ 2) * axisReflection) *
              planeRotation (Additive.toMul (circlePowerMod a q _ i)) := by rw [mul_assoc]
        _ = (axisReflection * planeRotation (squareRoot ^ 2)) *
              planeRotation (Additive.toMul (circlePowerMod a q _ i)) := by
            rw [halfTurn_commute_axisReflection]
        _ = axisReflection *
              (planeRotation (squareRoot ^ 2) *
                planeRotation (Additive.toMul (circlePowerMod a q _ i))) := by rw [mul_assoc]
        _ = axisReflection *
              (planeRotation (Additive.toMul (circlePowerMod a q _ i)) *
                planeRotation (squareRoot ^ 2)) := by rw [planeRotation_commute]
        _ = (axisReflection * planeRotation
              (Additive.toMul (circlePowerMod a q _ i))) *
                planeRotation (squareRoot ^ 2) := by rw [mul_assoc]

/-- Twist the reversing coset by the central half turn.  For rotation order three this changes
the integral reflection embedding from the full-axis-span form to the index-three form. -/
def halfTurnTwistedDihedralRepresentation
    (a : Circle) (q : ℕ) (horder : orderOf a = q) :
    DihedralGroup q →* (Plane ≃ₗᵢ[ℝ] Plane) where
  toFun
    | .r i => dihedralLinearRepresentation a q horder (.r i)
    | .sr i => planeRotation (squareRoot ^ 2) *
        dihedralLinearRepresentation a q horder (.sr i)
  map_one' := by
    change dihedralLinearRepresentation a q horder 1 = 1
    exact map_one _
  map_mul' x y := by
    let f := dihedralLinearRepresentation a q horder
    let H := planeRotation (squareRoot ^ 2)
    cases x with
    | r i =>
        cases y with
        | r j => simpa [f] using f.map_mul (.r i) (.r j)
        | sr j =>
            change H * f (.sr (j - i)) = f (.r i) * (H * f (.sr j))
            have hmul : f (.sr (j - i)) = f (.r i) * f (.sr j) := by
              simpa only [DihedralGroup.r_mul_sr] using f.map_mul (.r i) (.sr j)
            calc
              H * f (.sr (j - i)) = H * (f (.r i) * f (.sr j)) := by rw [hmul]
              _ = (H * f (.r i)) * f (.sr j) := (mul_assoc _ _ _).symm
              _ = (f (.r i) * H) * f (.sr j) := by
                rw [halfTurn_commute_dihedralLinearRepresentation]
              _ = f (.r i) * (H * f (.sr j)) := mul_assoc _ _ _
    | sr i =>
        cases y with
        | r j =>
            change H * f (.sr (i + j)) = (H * f (.sr i)) * f (.r j)
            have hmul : f (.sr (i + j)) = f (.sr i) * f (.r j) := by
              simpa only [DihedralGroup.sr_mul_r] using f.map_mul (.sr i) (.r j)
            calc
              H * f (.sr (i + j)) = H * (f (.sr i) * f (.r j)) := by rw [hmul]
              _ = (H * f (.sr i)) * f (.r j) := (mul_assoc _ _ _).symm
        | sr j =>
            change f (.r (j - i)) = (H * f (.sr i)) * (H * f (.sr j))
            have hmul : f (.r (j - i)) = f (.sr i) * f (.sr j) := by
              simpa only [DihedralGroup.sr_mul_sr] using f.map_mul (.sr i) (.sr j)
            calc
              f (.r (j - i)) = f (.sr i) * f (.sr j) := hmul
              _ = (H * H) * (f (.sr i) * f (.sr j)) := by rw [halfTurn_sq, one_mul]
              _ = H * (H * (f (.sr i) * f (.sr j))) := mul_assoc _ _ _
              _ = H * ((H * f (.sr i)) * f (.sr j)) := by
                rw [← mul_assoc H (f (.sr i)) (f (.sr j))]
              _ = H * ((f (.sr i) * H) * f (.sr j)) := by
                rw [halfTurn_commute_dihedralLinearRepresentation]
              _ = H * (f (.sr i) * (H * f (.sr j))) := by rw [mul_assoc]
              _ = (H * f (.sr i)) * (H * f (.sr j)) := (mul_assoc _ _ _).symm

/-- A half-turn-twisted reflection still has determinant `-1`. -/
theorem halfTurn_mul_axisReflection_mul_planeRotation_det (b : Circle) :
    LinearMap.det
      (((planeRotation (squareRoot ^ 2) *
        (axisReflection * planeRotation b)).toLinearEquiv : Plane →ₗ[ℝ] Plane)) = -1 := by
  change LinearMap.det
    ((planeRotation (squareRoot ^ 2)).toLinearEquiv.toLinearMap.comp
      (axisReflection * planeRotation b).toLinearEquiv.toLinearMap) = -1
  rw [LinearMap.det_comp, planeRotation_det, axisReflection_mul_planeRotation_det]
  norm_num

/-- A rotation cannot equal a half-turn-twisted reflection. -/
theorem planeRotation_ne_halfTurn_mul_axisReflection_mul_planeRotation (a b : Circle) :
    planeRotation a ≠
      planeRotation (squareRoot ^ 2) * (axisReflection * planeRotation b) := by
  intro h
  have hdet := congrArg
    (fun A : Plane ≃ₗᵢ[ℝ] Plane =>
      LinearMap.det (A.toLinearEquiv : Plane →ₗ[ℝ] Plane)) h
  rw [planeRotation_det, halfTurn_mul_axisReflection_mul_planeRotation_det] at hdet
  norm_num at hdet

/-- The half-turn twist remains faithful. -/
theorem halfTurnTwistedDihedralRepresentation_injective
    (a : Circle) (q : ℕ) (horder : orderOf a = q) :
    Function.Injective (halfTurnTwistedDihedralRepresentation a q horder) := by
  intro x y hxy
  cases x with
  | r i =>
      cases y with
      | r j =>
          exact dihedralLinearRepresentation_injective a q horder hxy
      | sr j =>
          exfalso
          change planeRotation
              (Additive.toMul (circlePowerMod a q _ i)) =
            planeRotation (squareRoot ^ 2) *
              (axisReflection * planeRotation
                (Additive.toMul (circlePowerMod a q _ j))) at hxy
          exact (planeRotation_ne_halfTurn_mul_axisReflection_mul_planeRotation _ _ hxy).elim
  | sr i =>
      cases y with
      | r j =>
          exfalso
          change planeRotation (squareRoot ^ 2) *
              (axisReflection * planeRotation
                (Additive.toMul (circlePowerMod a q _ i))) =
            planeRotation
              (Additive.toMul (circlePowerMod a q _ j)) at hxy
          exact (planeRotation_ne_halfTurn_mul_axisReflection_mul_planeRotation _ _ hxy.symm).elim
      | sr j =>
          apply dihedralLinearRepresentation_injective a q horder
          apply mul_left_cancel (a := planeRotation (squareRoot ^ 2))
          exact hxy

/-- Symmorphic data using the half-turn-twisted reflection embedding. -/
def twistedSymmorphicDihedralCosetData
    (L : RankTwoLattice Plane) (a : Circle) (q : ℕ) [NeZero q]
    (horder : orderOf a = q)
    (ha : planeRotation a ∈ latticeStabilizer L)
    (hs : axisReflection ∈ latticeStabilizer L) :
    FiniteCosetData (DihedralGroup q) where
  lattice := L
  linearRep := halfTurnTwistedDihedralRepresentation a q horder
  linearRep_injective := halfTurnTwistedDihedralRepresentation_injective a q horder
  preserves_lattice := by
    intro p
    cases p with
    | r i =>
        exact dihedralLinearRepresentation_mem_stabilizer L a q horder ha hs (.r i)
    | sr i =>
        exact (latticeStabilizer L).mul_mem (halfTurn_mem_stabilizer L)
          (dihedralLinearRepresentation_mem_stabilizer L a q horder ha hs (.sr i))
  shift := fun _ => 0
  shift_one_mem := L.carrier.zero_mem
  cocycle_mem := by simp

/-! ## Six symmorphic models among the nine multiple-reflection classes -/

def pmmCosetData : FiniteCosetData (DihedralGroup 2) :=
  symmorphicDihedralCosetData RankTwoLattice.standardLattice (squareRoot ^ 2) 2
    squareRoot_sq_order (halfTurn_mem_stabilizer _) axisReflection_mem_squareStabilizer

def cmmCosetData : FiniteCosetData (DihedralGroup 2) :=
  symmorphicDihedralCosetData centeredLattice (squareRoot ^ 2) 2
    squareRoot_sq_order (halfTurn_mem_stabilizer _) axisReflection_mem_centeredStabilizer

def p3m1CosetData : FiniteCosetData (DihedralGroup 3) :=
  symmorphicDihedralCosetData hexLattice (hexRoot ^ 2) 3 hexRoot_sq_order
    (by
      change planeRotationHom (hexRoot ^ 2) ∈ latticeStabilizer hexLattice
      rw [map_pow]
      exact (latticeStabilizer hexLattice).pow_mem hexRotation_mem_stabilizer 2)
    axisReflection_mem_hexStabilizer

def p31mCosetData : FiniteCosetData (DihedralGroup 3) :=
  twistedSymmorphicDihedralCosetData hexLattice (hexRoot ^ 2) 3 hexRoot_sq_order
    (by
      change planeRotationHom (hexRoot ^ 2) ∈ latticeStabilizer hexLattice
      rw [map_pow]
      exact (latticeStabilizer hexLattice).pow_mem hexRotation_mem_stabilizer 2)
    axisReflection_mem_hexStabilizer

def p4mCosetData : FiniteCosetData (DihedralGroup 4) :=
  symmorphicDihedralCosetData RankTwoLattice.standardLattice squareRoot 4
    squareRoot_order squareRotation_mem_stabilizer axisReflection_mem_squareStabilizer

def p6mCosetData : FiniteCosetData (DihedralGroup 6) :=
  symmorphicDihedralCosetData hexLattice hexRoot 6
    hexRoot_order hexRotation_mem_stabilizer axisReflection_mem_hexStabilizer

/-- Primitive rectangular model with two mirror families. -/
def pmmModel : PlaneGroup := finiteCosetPlaneGroup pmmCosetData

/-- Centered rectangular model with two mirror families. -/
def cmmModel : PlaneGroup := finiteCosetPlaneGroup cmmCosetData

/-- Triangular model whose reflection-axis spans generate the full lattice. -/
def p3m1Model : PlaneGroup := finiteCosetPlaneGroup p3m1CosetData

/-- Triangular model whose reflection-axis spans have index three. -/
def p31mModel : PlaneGroup := finiteCosetPlaneGroup p31mCosetData

/-- Square symmorphic dihedral model. -/
def p4mModel : PlaneGroup := finiteCosetPlaneGroup p4mCosetData

/-- Hexagonal symmorphic dihedral model. -/
def p6mModel : PlaneGroup := finiteCosetPlaneGroup p6mCosetData

@[simp] theorem pmmModel_translationLattice :
    pmmModel.translationLattice = RankTwoLattice.standardLattice := rfl

@[simp] theorem cmmModel_translationLattice :
    cmmModel.translationLattice = centeredLattice := rfl

@[simp] theorem p3m1Model_translationLattice :
    p3m1Model.translationLattice = hexLattice := rfl

@[simp] theorem p31mModel_translationLattice :
    p31mModel.translationLattice = hexLattice := rfl

@[simp] theorem p4mModel_translationLattice :
    p4mModel.translationLattice = RankTwoLattice.standardLattice := rfl

@[simp] theorem p6mModel_translationLattice :
    p6mModel.translationLattice = hexLattice := rfl

theorem pmmModel_pointGroup :
    pointGroup pmmModel.carrier = pmmCosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup pmmCosetData

theorem cmmModel_pointGroup :
    pointGroup cmmModel.carrier = cmmCosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup cmmCosetData

theorem p3m1Model_pointGroup :
    pointGroup p3m1Model.carrier = p3m1CosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup p3m1CosetData

theorem p31mModel_pointGroup :
    pointGroup p31mModel.carrier = p31mCosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup p31mCosetData

theorem p4mModel_pointGroup :
    pointGroup p4mModel.carrier = p4mCosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup p4mCosetData

theorem p6mModel_pointGroup :
    pointGroup p6mModel.carrier = p6mCosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup p6mCosetData

@[simp] theorem pmmModel_pointGroup_card : Nat.card (pointGroup pmmModel.carrier) = 4 := by
  calc
    Nat.card (pointGroup pmmModel.carrier) = Nat.card (DihedralGroup 2) := by
      simpa only [pmmModel] using finiteCosetPlaneGroup_pointGroup_card pmmCosetData
    _ = 4 := by rw [DihedralGroup.nat_card]

@[simp] theorem cmmModel_pointGroup_card : Nat.card (pointGroup cmmModel.carrier) = 4 := by
  calc
    Nat.card (pointGroup cmmModel.carrier) = Nat.card (DihedralGroup 2) := by
      simpa only [cmmModel] using finiteCosetPlaneGroup_pointGroup_card cmmCosetData
    _ = 4 := by rw [DihedralGroup.nat_card]

@[simp] theorem p3m1Model_pointGroup_card : Nat.card (pointGroup p3m1Model.carrier) = 6 := by
  calc
    Nat.card (pointGroup p3m1Model.carrier) = Nat.card (DihedralGroup 3) := by
      simpa only [p3m1Model] using finiteCosetPlaneGroup_pointGroup_card p3m1CosetData
    _ = 6 := by rw [DihedralGroup.nat_card]

@[simp] theorem p31mModel_pointGroup_card : Nat.card (pointGroup p31mModel.carrier) = 6 := by
  calc
    Nat.card (pointGroup p31mModel.carrier) = Nat.card (DihedralGroup 3) := by
      simpa only [p31mModel] using finiteCosetPlaneGroup_pointGroup_card p31mCosetData
    _ = 6 := by rw [DihedralGroup.nat_card]

@[simp] theorem p4mModel_pointGroup_card : Nat.card (pointGroup p4mModel.carrier) = 8 := by
  calc
    Nat.card (pointGroup p4mModel.carrier) = Nat.card (DihedralGroup 4) := by
      simpa only [p4mModel] using finiteCosetPlaneGroup_pointGroup_card p4mCosetData
    _ = 8 := by rw [DihedralGroup.nat_card]

@[simp] theorem p6mModel_pointGroup_card : Nat.card (pointGroup p6mModel.carrier) = 12 := by
  calc
    Nat.card (pointGroup p6mModel.carrier) = Nat.card (DihedralGroup 6) := by
      simpa only [p6mModel] using finiteCosetPlaneGroup_pointGroup_card p6mCosetData
    _ = 12 := by rw [DihedralGroup.nat_card]

/-! ## The three nonsymmorphic glide models -/

private def squareBasisZero : Plane :=
  (RankTwoLattice.standardLattice.basis 0 : Plane)

private def squareBasisOne : Plane :=
  (RankTwoLattice.standardLattice.basis 1 : Plane)

@[simp]
private theorem squareBasisZero_mem :
    squareBasisZero ∈ RankTwoLattice.standardLattice.carrier :=
  (RankTwoLattice.standardLattice.basis 0).property

@[simp]
private theorem squareBasisOne_mem :
    squareBasisOne ∈ RankTwoLattice.standardLattice.carrier :=
  (RankTwoLattice.standardLattice.basis 1).property

@[simp]
private theorem axisReflection_squareBasisZero :
    axisReflection squareBasisZero = squareBasisZero := by
  exact axisReflection_standard_basis_zero

@[simp]
private theorem axisReflection_squareBasisOne :
    axisReflection squareBasisOne = -squareBasisOne := by
  exact axisReflection_standard_basis_one

private theorem squareBasis_integer_combination_mem (m n : ℤ) :
    (m : ℝ) • squareBasisZero + (n : ℝ) • squareBasisOne ∈
      RankTwoLattice.standardLattice.carrier := by
  have hm := RankTwoLattice.standardLattice.carrier.smul_mem m squareBasisZero_mem
  have hn := RankTwoLattice.standardLattice.carrier.smul_mem n squareBasisOne_mem
  rw [← Int.cast_smul_eq_zsmul ℝ] at hm hn
  exact RankTwoLattice.standardLattice.carrier.add_mem hm hn

@[simp]
theorem pmmCosetData_linearRep_r_zero :
    pmmCosetData.linearRep (.r 0) = 1 := by
  change planeRotation
      (Additive.toMul (circlePowerMod (squareRoot ^ 2) 2 _ 0)) = 1
  rw [circlePowerMod_zero, planeRotation_one]

@[simp]
theorem pmmCosetData_linearRep_r_one :
    pmmCosetData.linearRep (.r 1) = planeRotation (squareRoot ^ 2) := by
  change planeRotation
      (Additive.toMul (circlePowerMod (squareRoot ^ 2) 2 _ 1)) =
    planeRotation (squareRoot ^ 2)
  apply congrArg planeRotation
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num,
    circlePowerMod_coe]
  simp

@[simp]
theorem pmmCosetData_linearRep_sr_zero :
    pmmCosetData.linearRep (.sr 0) = axisReflection := by
  change axisReflection * planeRotation
      (Additive.toMul (circlePowerMod (squareRoot ^ 2) 2 _ 0)) = axisReflection
  rw [circlePowerMod_zero, planeRotation_one, mul_one]

@[simp]
theorem pmmCosetData_linearRep_sr_one :
    pmmCosetData.linearRep (.sr 1) =
      axisReflection * planeRotation (squareRoot ^ 2) := by
  change axisReflection * planeRotation
      (Additive.toMul (circlePowerMod (squareRoot ^ 2) 2 _ 1)) =
    axisReflection * planeRotation (squareRoot ^ 2)
  congr 1
  apply congrArg planeRotation
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num,
    circlePowerMod_coe]
  simp

@[simp] private theorem pmmLinear_r_zero_squareBasisZero :
    pmmCosetData.linearRep (.r 0) squareBasisZero = squareBasisZero := by
  rw [pmmCosetData_linearRep_r_zero]
  rfl

@[simp] private theorem pmmLinear_r_zero_squareBasisOne :
    pmmCosetData.linearRep (.r 0) squareBasisOne = squareBasisOne := by
  rw [pmmCosetData_linearRep_r_zero]
  rfl

@[simp] private theorem pmmLinear_r_one_squareBasisZero :
    pmmCosetData.linearRep (.r 1) squareBasisZero = -squareBasisZero := by
  rw [pmmCosetData_linearRep_r_one, halfTurn_apply]

@[simp] private theorem pmmLinear_r_one_squareBasisOne :
    pmmCosetData.linearRep (.r 1) squareBasisOne = -squareBasisOne := by
  rw [pmmCosetData_linearRep_r_one, halfTurn_apply]

@[simp] private theorem pmmLinear_sr_zero_squareBasisZero :
    pmmCosetData.linearRep (.sr 0) squareBasisZero = squareBasisZero := by
  rw [pmmCosetData_linearRep_sr_zero, axisReflection_squareBasisZero]

@[simp] private theorem pmmLinear_sr_zero_squareBasisOne :
    pmmCosetData.linearRep (.sr 0) squareBasisOne = -squareBasisOne := by
  rw [pmmCosetData_linearRep_sr_zero, axisReflection_squareBasisOne]

@[simp] private theorem pmmLinear_sr_one_squareBasisZero :
    pmmCosetData.linearRep (.sr 1) squareBasisZero = -squareBasisZero := by
  rw [pmmCosetData_linearRep_sr_one]
  change axisReflection (planeRotation (squareRoot ^ 2) squareBasisZero) =
    -squareBasisZero
  rw [halfTurn_apply, map_neg, axisReflection_squareBasisZero]

@[simp] private theorem pmmLinear_sr_one_squareBasisOne :
    pmmCosetData.linearRep (.sr 1) squareBasisOne = squareBasisOne := by
  rw [pmmCosetData_linearRep_sr_one]
  change axisReflection (planeRotation (squareRoot ^ 2) squareBasisOne) =
    squareBasisOne
  rw [halfTurn_apply, map_neg, axisReflection_squareBasisOne, neg_neg]

/-- The `pmg` coset section: one reflection family is mirrored and the other has half-period
glide. -/
def pmgShift : DihedralGroup 2 → Plane
  | .r i => match i.val with
    | 0 => 0
    | _ => -(1 / 2 : ℝ) • squareBasisOne
  | .sr i => match i.val with
    | 0 => 0
    | _ => (1 / 2 : ℝ) • squareBasisOne

@[simp] private theorem pmgShift_r_zero : pmgShift (.r 0) = 0 := by
  change (match (0 : ZMod 2).val with
    | 0 => 0
    | _ => -(1 / 2 : ℝ) • squareBasisOne) = 0
  rw [ZMod.val_zero]
  rfl

@[simp] private theorem pmgShift_r_one :
    pmgShift (.r 1) = -(1 / 2 : ℝ) • squareBasisOne := by
  change (match (1 : ZMod 2).val with
    | 0 => 0
    | _ => -(1 / 2 : ℝ) • squareBasisOne) = _
  rw [ZMod.val_one]
  rfl

@[simp] private theorem pmgShift_sr_zero : pmgShift (.sr 0) = 0 := by
  change (match (0 : ZMod 2).val with
    | 0 => 0
    | _ => (1 / 2 : ℝ) • squareBasisOne) = 0
  rw [ZMod.val_zero]
  rfl

@[simp] private theorem pmgShift_sr_one :
    pmgShift (.sr 1) = (1 / 2 : ℝ) • squareBasisOne := by
  change (match (1 : ZMod 2).val with
    | 0 => 0
    | _ => (1 / 2 : ℝ) • squareBasisOne) = _
  rw [ZMod.val_one]
  rfl

@[simp] private theorem pmgShift_one : pmgShift 1 = 0 := by
  rw [DihedralGroup.one_def, pmgShift_r_zero]

@[simp] private theorem pmgShift_r_two : pmgShift (.r (2 : ZMod 2)) = 0 := by
  rw [show (2 : ZMod 2) = 0 by decide, pmgShift_r_zero]

@[simp] private theorem pmgShift_sr_two : pmgShift (.sr (2 : ZMod 2)) = 0 := by
  rw [show (2 : ZMod 2) = 0 by decide, pmgShift_sr_zero]

@[simp] private theorem pmgShift_r_neg_one :
    pmgShift (.r (-1 : ZMod 2)) = -(1 / 2 : ℝ) • squareBasisOne := by
  rw [show (-1 : ZMod 2) = 1 by decide, pmgShift_r_one]

@[simp] private theorem pmgShift_sr_neg_one :
    pmgShift (.sr (-1 : ZMod 2)) = (1 / 2 : ℝ) • squareBasisOne := by
  rw [show (-1 : ZMod 2) = 1 by decide, pmgShift_sr_one]

/-- The `pgg` coset section: both primitive reflection families have nonzero half-period glide. -/
def pggShift : DihedralGroup 2 → Plane
  | .r i => match i.val with
    | 0 => 0
    | _ => (1 / 2 : ℝ) • (squareBasisZero - squareBasisOne)
  | .sr i => match i.val with
    | 0 => (1 / 2 : ℝ) • squareBasisZero
    | _ => (1 / 2 : ℝ) • squareBasisOne

@[simp] private theorem pggShift_r_zero : pggShift (.r 0) = 0 := by
  change (match (0 : ZMod 2).val with
    | 0 => 0
    | _ => (1 / 2 : ℝ) • (squareBasisZero - squareBasisOne)) = 0
  rw [ZMod.val_zero]
  rfl

@[simp] private theorem pggShift_r_one :
    pggShift (.r 1) = (1 / 2 : ℝ) • (squareBasisZero - squareBasisOne) := by
  change (match (1 : ZMod 2).val with
    | 0 => 0
    | _ => (1 / 2 : ℝ) • (squareBasisZero - squareBasisOne)) = _
  rw [ZMod.val_one]
  rfl

@[simp] private theorem pggShift_sr_zero :
    pggShift (.sr 0) = (1 / 2 : ℝ) • squareBasisZero := by
  change (match (0 : ZMod 2).val with
    | 0 => (1 / 2 : ℝ) • squareBasisZero
    | _ => (1 / 2 : ℝ) • squareBasisOne) = _
  rw [ZMod.val_zero]
  rfl

@[simp] private theorem pggShift_sr_one :
    pggShift (.sr 1) = (1 / 2 : ℝ) • squareBasisOne := by
  change (match (1 : ZMod 2).val with
    | 0 => (1 / 2 : ℝ) • squareBasisZero
    | _ => (1 / 2 : ℝ) • squareBasisOne) = _
  rw [ZMod.val_one]
  rfl

@[simp] private theorem pggShift_one : pggShift 1 = 0 := by
  rw [DihedralGroup.one_def, pggShift_r_zero]

@[simp] private theorem pggShift_r_two : pggShift (.r (2 : ZMod 2)) = 0 := by
  rw [show (2 : ZMod 2) = 0 by decide, pggShift_r_zero]

@[simp] private theorem pggShift_sr_two :
    pggShift (.sr (2 : ZMod 2)) = (1 / 2 : ℝ) • squareBasisZero := by
  rw [show (2 : ZMod 2) = 0 by decide, pggShift_sr_zero]

@[simp] private theorem pggShift_r_neg_one :
    pggShift (.r (-1 : ZMod 2)) =
      (1 / 2 : ℝ) • (squareBasisZero - squareBasisOne) := by
  rw [show (-1 : ZMod 2) = 1 by decide, pggShift_r_one]

@[simp] private theorem pggShift_sr_neg_one :
    pggShift (.sr (-1 : ZMod 2)) = (1 / 2 : ℝ) • squareBasisOne := by
  rw [show (-1 : ZMod 2) = 1 by decide, pggShift_sr_one]

private theorem zmod_two_eq_zero_or_one (i : ZMod 2) : i = 0 ∨ i = 1 := by
  have hlt := i.val_lt
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · left
    calc
      i = (i.val : ZMod 2) := (ZMod.natCast_zmod_val i).symm
      _ = 0 := by simp [hi]
  · right
    calc
      i = (i.val : ZMod 2) := (ZMod.natCast_zmod_val i).symm
      _ = 1 := by simp [hi]

private theorem pmgShift_cocycle_mem (p q : DihedralGroup 2) :
    pmgShift p + pmmCosetData.linearRep p (pmgShift q) - pmgShift (p * q) ∈
      RankTwoLattice.standardLattice.carrier := by
  cases p <;> rename_i i
  all_goals rcases zmod_two_eq_zero_or_one i with rfl | rfl
  all_goals cases q <;> rename_i j
  all_goals rcases zmod_two_eq_zero_or_one j with rfl | rfl
  all_goals norm_num only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
    DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, pmgShift_r_zero,
    pmgShift_r_one, pmgShift_sr_zero, pmgShift_sr_one, pmgShift_one,
    pmgShift_r_two, pmgShift_sr_two, pmgShift_r_neg_one, pmgShift_sr_neg_one,
    pmmLinear_r_zero_squareBasisZero, pmmLinear_r_zero_squareBasisOne,
    pmmLinear_r_one_squareBasisZero, pmmLinear_r_one_squareBasisOne,
    pmmLinear_sr_zero_squareBasisZero, pmmLinear_sr_zero_squareBasisOne,
    pmmLinear_sr_one_squareBasisZero, pmmLinear_sr_one_squareBasisOne,
    map_zero, map_neg, map_smul, one_apply, mul_apply, halfTurn_apply,
    axisReflection_squareBasisZero, axisReflection_squareBasisOne,
    zero_add, add_zero, sub_zero, zero_sub]
  all_goals solve
    | (convert squareBasis_integer_combination_mem 0 0 using 1; module)
    | (convert squareBasis_integer_combination_mem 1 0 using 1; module)
    | (convert squareBasis_integer_combination_mem (-1) 0 using 1; module)
    | (convert squareBasis_integer_combination_mem 0 1 using 1; module)
    | (convert squareBasis_integer_combination_mem 0 (-1) using 1; module)

private theorem pggShift_cocycle_mem (p q : DihedralGroup 2) :
    pggShift p + pmmCosetData.linearRep p (pggShift q) - pggShift (p * q) ∈
      RankTwoLattice.standardLattice.carrier := by
  cases p <;> rename_i i
  all_goals rcases zmod_two_eq_zero_or_one i with rfl | rfl
  all_goals cases q <;> rename_i j
  all_goals rcases zmod_two_eq_zero_or_one j with rfl | rfl
  all_goals norm_num only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
    DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, pggShift_r_zero,
    pggShift_r_one, pggShift_sr_zero, pggShift_sr_one, pggShift_one,
    pggShift_r_two, pggShift_sr_two, pggShift_r_neg_one, pggShift_sr_neg_one,
    pmmLinear_r_zero_squareBasisZero, pmmLinear_r_zero_squareBasisOne,
    pmmLinear_r_one_squareBasisZero, pmmLinear_r_one_squareBasisOne,
    pmmLinear_sr_zero_squareBasisZero, pmmLinear_sr_zero_squareBasisOne,
    pmmLinear_sr_one_squareBasisZero, pmmLinear_sr_one_squareBasisOne,
    map_zero, map_neg, map_add, map_sub, map_smul, one_apply, mul_apply,
    halfTurn_apply, axisReflection_squareBasisZero,
    axisReflection_squareBasisOne, zero_add, add_zero, sub_zero, zero_sub]
  all_goals solve
    | (convert squareBasis_integer_combination_mem 0 0 using 1; module)
    | (convert squareBasis_integer_combination_mem 1 0 using 1; module)
    | (convert squareBasis_integer_combination_mem (-1) 0 using 1; module)
    | (convert squareBasis_integer_combination_mem 0 1 using 1; module)
    | (convert squareBasis_integer_combination_mem 0 (-1) using 1; module)
    | (convert squareBasis_integer_combination_mem 1 1 using 1; module)
    | (convert squareBasis_integer_combination_mem 1 (-1) using 1; module)
    | (convert squareBasis_integer_combination_mem (-1) 1 using 1; module)

def pmgCosetData : FiniteCosetData (DihedralGroup 2) where
  lattice := RankTwoLattice.standardLattice
  linearRep := pmmCosetData.linearRep
  linearRep_injective := pmmCosetData.linearRep_injective
  preserves_lattice := pmmCosetData.preserves_lattice
  shift := pmgShift
  shift_one_mem := by
    change pmgShift (.r 0) ∈ RankTwoLattice.standardLattice.carrier
    simp [pmgShift]
  cocycle_mem := pmgShift_cocycle_mem

def pggCosetData : FiniteCosetData (DihedralGroup 2) where
  lattice := RankTwoLattice.standardLattice
  linearRep := pmmCosetData.linearRep
  linearRep_injective := pmmCosetData.linearRep_injective
  preserves_lattice := pmmCosetData.preserves_lattice
  shift := pggShift
  shift_one_mem := by
    change pggShift (.r 0) ∈ RankTwoLattice.standardLattice.carrier
    simp [pggShift]
  cocycle_mem := pggShift_cocycle_mem

/-- Primitive rectangular model with one mirror and one glide-reflection family. -/
def pmgModel : PlaneGroup := finiteCosetPlaneGroup pmgCosetData

/-- Primitive rectangular model with two glide-reflection families. -/
def pggModel : PlaneGroup := finiteCosetPlaneGroup pggCosetData

@[simp] theorem pmgModel_translationLattice :
    pmgModel.translationLattice = RankTwoLattice.standardLattice := rfl

@[simp] theorem pggModel_translationLattice :
    pggModel.translationLattice = RankTwoLattice.standardLattice := rfl

theorem pmgModel_pointGroup :
    pointGroup pmgModel.carrier = pmgCosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup pmgCosetData

theorem pggModel_pointGroup :
    pointGroup pggModel.carrier = pggCosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup pggCosetData

@[simp] theorem pmgModel_pointGroup_card : Nat.card (pointGroup pmgModel.carrier) = 4 := by
  calc
    Nat.card (pointGroup pmgModel.carrier) = Nat.card (DihedralGroup 2) := by
      simpa only [pmgModel] using finiteCosetPlaneGroup_pointGroup_card pmgCosetData
    _ = 4 := by rw [DihedralGroup.nat_card]

@[simp] theorem pggModel_pointGroup_card : Nat.card (pointGroup pggModel.carrier) = 4 := by
  calc
    Nat.card (pointGroup pggModel.carrier) = Nat.card (DihedralGroup 2) := by
      simpa only [pggModel] using finiteCosetPlaneGroup_pointGroup_card pggCosetData
    _ = 4 := by rw [DihedralGroup.nat_card]

@[simp]
theorem squareQuarterTurn_basis_zero :
    planeRotation squareRoot squareBasisZero = squareBasisOne := by
  change planeRotation squareRoot
      (RankTwoLattice.standardLattice.basis 0 : Plane) =
    (RankTwoLattice.standardLattice.basis 1 : Plane)
  apply coordinateIsometry.injective
  rw [coordinateIsometry_planeRotation,
    coordinateIsometry_squareLattice_basis_zero,
    coordinateIsometry_squareLattice_basis_one]
  simp [squareRoot]

@[simp]
theorem squareQuarterTurn_basis_one :
    planeRotation squareRoot squareBasisOne = -squareBasisZero := by
  change planeRotation squareRoot
      (RankTwoLattice.standardLattice.basis 1 : Plane) =
    -(RankTwoLattice.standardLattice.basis 0 : Plane)
  apply coordinateIsometry.injective
  rw [coordinateIsometry_planeRotation,
    coordinateIsometry_squareLattice_basis_one, map_neg,
    coordinateIsometry_squareLattice_basis_zero]
  simp [squareRoot, Complex.I_mul_I]

@[simp]
theorem squareHalfTurn_basis_zero :
    planeRotation (squareRoot ^ 2) squareBasisZero = -squareBasisZero :=
  halfTurn_apply squareBasisZero

@[simp]
theorem squareHalfTurn_basis_one :
    planeRotation (squareRoot ^ 2) squareBasisOne = -squareBasisOne :=
  halfTurn_apply squareBasisOne

@[simp]
theorem squareThreeQuarterTurn_basis_zero :
    planeRotation (squareRoot ^ 3) squareBasisZero = -squareBasisOne := by
  calc
    planeRotation (squareRoot ^ 3) squareBasisZero =
        planeRotation (squareRoot ^ 2 * squareRoot) squareBasisZero := by group
    _ = (planeRotation (squareRoot ^ 2) * planeRotation squareRoot)
        squareBasisZero := by rw [planeRotation_mul]
    _ = planeRotation (squareRoot ^ 2)
        (planeRotation squareRoot squareBasisZero) := by
      simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    _ = -squareBasisOne := by
      rw [squareQuarterTurn_basis_zero, squareHalfTurn_basis_one]

@[simp]
theorem squareThreeQuarterTurn_basis_one :
    planeRotation (squareRoot ^ 3) squareBasisOne = squareBasisZero := by
  calc
    planeRotation (squareRoot ^ 3) squareBasisOne =
        planeRotation (squareRoot ^ 2 * squareRoot) squareBasisOne := by group
    _ = (planeRotation (squareRoot ^ 2) * planeRotation squareRoot)
        squareBasisOne := by rw [planeRotation_mul]
    _ = planeRotation (squareRoot ^ 2)
        (planeRotation squareRoot squareBasisOne) := by
      simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    _ = squareBasisZero := by
      rw [squareQuarterTurn_basis_one, map_neg, squareHalfTurn_basis_zero, neg_neg]

@[simp]
theorem p4mCosetData_linearRep_r_zero :
    p4mCosetData.linearRep (.r 0) = 1 := by
  change planeRotation
      (Additive.toMul (circlePowerMod squareRoot 4 _ 0)) = 1
  rw [circlePowerMod_zero, planeRotation_one]

@[simp]
theorem p4mCosetData_linearRep_r_one :
    p4mCosetData.linearRep (.r 1) = planeRotation squareRoot := by
  change planeRotation
      (Additive.toMul (circlePowerMod squareRoot 4 _ 1)) =
    planeRotation squareRoot
  apply congrArg planeRotation
  rw [show (1 : ZMod 4) = ((1 : ℤ) : ZMod 4) by norm_num,
    circlePowerMod_coe]
  simp

@[simp]
theorem p4mCosetData_linearRep_r_two :
    p4mCosetData.linearRep (.r 2) = planeRotation (squareRoot ^ 2) := by
  change planeRotation
      (Additive.toMul (circlePowerMod squareRoot 4 _ 2)) =
    planeRotation (squareRoot ^ 2)
  apply congrArg planeRotation
  rw [show (2 : ZMod 4) = ((2 : ℤ) : ZMod 4) by norm_num,
    circlePowerMod_coe]
  rfl

@[simp]
theorem p4mCosetData_linearRep_r_three :
    p4mCosetData.linearRep (.r 3) = planeRotation (squareRoot ^ 3) := by
  change planeRotation
      (Additive.toMul (circlePowerMod squareRoot 4 _ 3)) =
    planeRotation (squareRoot ^ 3)
  apply congrArg planeRotation
  rw [show (3 : ZMod 4) = ((3 : ℤ) : ZMod 4) by norm_num,
    circlePowerMod_coe]
  rfl

theorem p4mCosetData_linearRep_sr_eq (i : ZMod 4) :
    p4mCosetData.linearRep (.sr i) =
      axisReflection * p4mCosetData.linearRep (.r i) :=
  rfl

@[simp]
theorem p4mCosetData_linearRep_sr_zero :
    p4mCosetData.linearRep (.sr 0) = axisReflection := by
  rw [p4mCosetData_linearRep_sr_eq, p4mCosetData_linearRep_r_zero, mul_one]

@[simp]
theorem p4mCosetData_linearRep_sr_one :
    p4mCosetData.linearRep (.sr 1) =
      axisReflection * planeRotation squareRoot := by
  rw [p4mCosetData_linearRep_sr_eq, p4mCosetData_linearRep_r_one]

@[simp]
theorem p4mCosetData_linearRep_sr_two :
    p4mCosetData.linearRep (.sr 2) =
      axisReflection * planeRotation (squareRoot ^ 2) := by
  rw [p4mCosetData_linearRep_sr_eq, p4mCosetData_linearRep_r_two]

@[simp]
theorem p4mCosetData_linearRep_sr_three :
    p4mCosetData.linearRep (.sr 3) =
      axisReflection * planeRotation (squareRoot ^ 3) := by
  rw [p4mCosetData_linearRep_sr_eq, p4mCosetData_linearRep_r_three]

/-- The half-diagonal glide vector in the `p4g` normal form. -/
def p4gGlideShift : Plane :=
  (1 / 2 : ℝ) • (squareBasisZero + squareBasisOne)

@[simp] private theorem p4mLinear_r_zero_p4gGlideShift :
    p4mCosetData.linearRep (.r 0) p4gGlideShift = p4gGlideShift := by
  rw [p4mCosetData_linearRep_r_zero]
  rfl

@[simp] private theorem p4mLinear_r_one_p4gGlideShift :
    p4mCosetData.linearRep (.r 1) p4gGlideShift =
      (1 / 2 : ℝ) • (-squareBasisZero + squareBasisOne) := by
  rw [p4mCosetData_linearRep_r_one, p4gGlideShift, map_smul, map_add,
    squareQuarterTurn_basis_zero, squareQuarterTurn_basis_one]
  module

@[simp] private theorem p4mLinear_r_two_p4gGlideShift :
    p4mCosetData.linearRep (.r 2) p4gGlideShift = -p4gGlideShift := by
  rw [p4mCosetData_linearRep_r_two, p4gGlideShift, map_smul, map_add,
    squareHalfTurn_basis_zero, squareHalfTurn_basis_one]
  module

@[simp] private theorem p4mLinear_r_three_p4gGlideShift :
    p4mCosetData.linearRep (.r 3) p4gGlideShift =
      (1 / 2 : ℝ) • (squareBasisZero - squareBasisOne) := by
  rw [p4mCosetData_linearRep_r_three, p4gGlideShift, map_smul, map_add,
    squareThreeQuarterTurn_basis_zero, squareThreeQuarterTurn_basis_one]
  module

@[simp] private theorem p4mLinear_sr_zero_p4gGlideShift :
    p4mCosetData.linearRep (.sr 0) p4gGlideShift =
      (1 / 2 : ℝ) • (squareBasisZero - squareBasisOne) := by
  rw [p4mCosetData_linearRep_sr_zero, p4gGlideShift, map_smul, map_add,
    axisReflection_squareBasisZero, axisReflection_squareBasisOne]
  module

@[simp] private theorem p4mLinear_sr_one_p4gGlideShift :
    p4mCosetData.linearRep (.sr 1) p4gGlideShift = -p4gGlideShift := by
  rw [p4mCosetData_linearRep_sr_one]
  change axisReflection (planeRotation squareRoot p4gGlideShift) = -p4gGlideShift
  rw [p4gGlideShift, map_smul, map_add, squareQuarterTurn_basis_zero,
    squareQuarterTurn_basis_one, map_smul, map_add]
  simp only [map_neg, axisReflection_squareBasisZero, axisReflection_squareBasisOne]
  module

@[simp] private theorem p4mLinear_sr_two_p4gGlideShift :
    p4mCosetData.linearRep (.sr 2) p4gGlideShift =
      (1 / 2 : ℝ) • (-squareBasisZero + squareBasisOne) := by
  rw [p4mCosetData_linearRep_sr_two]
  change axisReflection (planeRotation (squareRoot ^ 2) p4gGlideShift) =
    (1 / 2 : ℝ) • (-squareBasisZero + squareBasisOne)
  rw [p4gGlideShift, map_smul, map_add, squareHalfTurn_basis_zero,
    squareHalfTurn_basis_one, map_smul, map_add]
  simp only [map_neg, axisReflection_squareBasisZero, axisReflection_squareBasisOne]
  module

@[simp] private theorem p4mLinear_sr_three_p4gGlideShift :
    p4mCosetData.linearRep (.sr 3) p4gGlideShift = p4gGlideShift := by
  rw [p4mCosetData_linearRep_sr_three]
  change axisReflection (planeRotation (squareRoot ^ 3) p4gGlideShift) = p4gGlideShift
  rw [p4gGlideShift, map_smul, map_add, squareThreeQuarterTurn_basis_zero,
    squareThreeQuarterTurn_basis_one, map_smul, map_add]
  simp only [map_neg, axisReflection_squareBasisZero, axisReflection_squareBasisOne]
  module

/-- The `p4g` finite-coset section.  Rotation cosets are unshifted and every reversing coset uses
the same half-diagonal glide representative. -/
def p4gShift : DihedralGroup 4 → Plane
  | .r _ => 0
  | .sr _ => p4gGlideShift

@[simp] theorem p4gShift_r (i : ZMod 4) : p4gShift (.r i) = 0 := rfl

@[simp] theorem p4gShift_sr (i : ZMod 4) : p4gShift (.sr i) = p4gGlideShift := rfl

@[simp] theorem p4gShift_one : p4gShift 1 = 0 := by
  rw [DihedralGroup.one_def, p4gShift_r]

private theorem zmod_four_eq_zero_or_one_or_two_or_three (i : ZMod 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hlt := i.val_lt
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hi with hi | hi | hi | hi
  · left
    calc
      i = (i.val : ZMod 4) := (ZMod.natCast_zmod_val i).symm
      _ = 0 := by simp [hi]
  · right; left
    calc
      i = (i.val : ZMod 4) := (ZMod.natCast_zmod_val i).symm
      _ = 1 := by simp [hi]
  · right; right; left
    calc
      i = (i.val : ZMod 4) := (ZMod.natCast_zmod_val i).symm
      _ = 2 := by simp [hi]
  · right; right; right
    calc
      i = (i.val : ZMod 4) := (ZMod.natCast_zmod_val i).symm
      _ = 3 := by simp [hi]

private theorem p4g_rotation_glide_sub_mem (i : ZMod 4) :
    p4mCosetData.linearRep (.r i) p4gGlideShift - p4gGlideShift ∈
      RankTwoLattice.standardLattice.carrier := by
  rcases zmod_four_eq_zero_or_one_or_two_or_three i with
    rfl | rfl | rfl | rfl
  all_goals norm_num only [p4mLinear_r_zero_p4gGlideShift,
    p4mLinear_r_one_p4gGlideShift, p4mLinear_r_two_p4gGlideShift,
    p4mLinear_r_three_p4gGlideShift]
  all_goals simp only [p4gGlideShift]
  all_goals solve
    | (convert squareBasis_integer_combination_mem 0 0 using 1; module)
    | (convert squareBasis_integer_combination_mem 1 0 using 1; module)
    | (convert squareBasis_integer_combination_mem (-1) 0 using 1; module)
    | (convert squareBasis_integer_combination_mem 0 1 using 1; module)
    | (convert squareBasis_integer_combination_mem 0 (-1) using 1; module)
    | (convert squareBasis_integer_combination_mem 1 1 using 1; module)
    | (convert squareBasis_integer_combination_mem 1 (-1) using 1; module)
    | (convert squareBasis_integer_combination_mem (-1) 1 using 1; module)
    | (convert squareBasis_integer_combination_mem (-1) (-1) using 1; module)

private theorem p4g_reflection_glide_add_mem (i : ZMod 4) :
    p4gGlideShift + p4mCosetData.linearRep (.sr i) p4gGlideShift ∈
      RankTwoLattice.standardLattice.carrier := by
  rcases zmod_four_eq_zero_or_one_or_two_or_three i with
    rfl | rfl | rfl | rfl
  all_goals norm_num only [p4mLinear_sr_zero_p4gGlideShift,
    p4mLinear_sr_one_p4gGlideShift, p4mLinear_sr_two_p4gGlideShift,
    p4mLinear_sr_three_p4gGlideShift]
  all_goals simp only [p4gGlideShift]
  all_goals solve
    | (convert squareBasis_integer_combination_mem 0 0 using 1; module)
    | (convert squareBasis_integer_combination_mem 1 0 using 1; module)
    | (convert squareBasis_integer_combination_mem (-1) 0 using 1; module)
    | (convert squareBasis_integer_combination_mem 0 1 using 1; module)
    | (convert squareBasis_integer_combination_mem 0 (-1) using 1; module)
    | (convert squareBasis_integer_combination_mem 1 1 using 1; module)

private theorem p4gShift_cocycle_mem (p q : DihedralGroup 4) :
    p4gShift p + p4mCosetData.linearRep p (p4gShift q) - p4gShift (p * q) ∈
      RankTwoLattice.standardLattice.carrier := by
  cases p with
  | r i =>
      cases q with
      | r j => simp only [DihedralGroup.r_mul_r, p4gShift_r, map_zero,
          zero_add, sub_self, Submodule.zero_mem]
      | sr j =>
          simpa only [DihedralGroup.r_mul_sr, p4gShift_r, p4gShift_sr,
            zero_add] using p4g_rotation_glide_sub_mem i
  | sr i =>
      cases q with
      | r j => simp only [DihedralGroup.sr_mul_r, p4gShift_sr, p4gShift_r,
          map_zero, add_zero, sub_self, Submodule.zero_mem]
      | sr j =>
          simpa only [DihedralGroup.sr_mul_sr, p4gShift_sr, p4gShift_r,
            sub_zero] using p4g_reflection_glide_add_mem i

def p4gCosetData : FiniteCosetData (DihedralGroup 4) where
  lattice := RankTwoLattice.standardLattice
  linearRep := p4mCosetData.linearRep
  linearRep_injective := p4mCosetData.linearRep_injective
  preserves_lattice := p4mCosetData.preserves_lattice
  shift := p4gShift
  shift_one_mem := by
    change p4gShift (.r 0) ∈ RankTwoLattice.standardLattice.carrier
    simp [p4gShift]
  cocycle_mem := p4gShift_cocycle_mem

/-- Square nonsymmorphic dihedral model. -/
def p4gModel : PlaneGroup := finiteCosetPlaneGroup p4gCosetData

@[simp] theorem p4gModel_translationLattice :
    p4gModel.translationLattice = RankTwoLattice.standardLattice := rfl

theorem p4gModel_pointGroup :
    pointGroup p4gModel.carrier = p4gCosetData.linearRep.range :=
  finiteCosetPlaneGroup_pointGroup p4gCosetData

@[simp] theorem p4gModel_pointGroup_card : Nat.card (pointGroup p4gModel.carrier) = 8 := by
  calc
    Nat.card (pointGroup p4gModel.carrier) = Nat.card (DihedralGroup 4) := by
      simpa only [p4gModel] using finiteCosetPlaneGroup_pointGroup_card p4gCosetData
    _ = 8 := by rw [DihedralGroup.nat_card]

/-! ## Nine-label model family -/

/-- The nine wallpaper types whose point group contains more than one reflection. -/
inductive MultipleReflectionType
  | cmm
  | pmm
  | pmg
  | pgg
  | p3m1
  | p31m
  | p4m
  | p4g
  | p6m
  deriving DecidableEq

instance : Fintype MultipleReflectionType where
  elems := {.cmm, .pmm, .pmg, .pgg, .p3m1, .p31m, .p4m, .p4g, .p6m}
  complete w := by cases w <;> simp

/-- The transparent standard model attached to a multiple-reflection label. -/
def MultipleReflectionType.model : MultipleReflectionType → PlaneGroup
  | .cmm => cmmModel
  | .pmm => pmmModel
  | .pmg => pmgModel
  | .pgg => pggModel
  | .p3m1 => p3m1Model
  | .p31m => p31mModel
  | .p4m => p4mModel
  | .p4g => p4gModel
  | .p6m => p6mModel

/-- Rotation order associated to a multiple-reflection standard model. -/
def MultipleReflectionType.rotationOrder : MultipleReflectionType → ℕ
  | .cmm | .pmm | .pmg | .pgg => 2
  | .p3m1 | .p31m => 3
  | .p4m | .p4g => 4
  | .p6m => 6

@[simp]
theorem MultipleReflectionType.model_pointGroup_card (w : MultipleReflectionType) :
    Nat.card (pointGroup w.model.carrier) = 2 * w.rotationOrder := by
  cases w <;> simp [MultipleReflectionType.model, MultipleReflectionType.rotationOrder]

@[simp]
theorem MultipleReflectionType.model_translationLattice (w : MultipleReflectionType) :
    w.model.translationLattice =
      match w with
      | .cmm => centeredLattice
      | .p3m1 | .p31m | .p6m => hexLattice
      | _ => RankTwoLattice.standardLattice := by
  cases w <;> rfl

/-! ## Canonical dihedral generators for finite-coset models -/

/-- The point-coordinate embedding of a finite-coset model is injective. -/
theorem finiteCosetPointElement_injective {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) : Function.Injective (finiteCosetPointElement D) := by
  intro p q hpq
  apply D.linearRep_injective
  exact congrArg Subtype.val hpq

@[simp]
theorem dihedralLinearRepresentation_det_r
    (a : Circle) (q : ℕ) (horder : orderOf a = q) (i : ZMod q) :
    LinearMap.det
        (((dihedralLinearRepresentation a q horder) (.r i)).toLinearEquiv :
          Plane →ₗ[ℝ] Plane) = 1 := by
  simp [dihedralLinearRepresentation, planeRotation_det]

@[simp]
theorem dihedralLinearRepresentation_det_sr
    (a : Circle) (q : ℕ) (horder : orderOf a = q) (i : ZMod q) :
    LinearMap.det
        (((dihedralLinearRepresentation a q horder) (.sr i)).toLinearEquiv :
          Plane →ₗ[ℝ] Plane) = -1 := by
  simp [dihedralLinearRepresentation, axisReflection_mul_planeRotation_det]

@[simp]
theorem halfTurnTwistedDihedralRepresentation_det_r
    (a : Circle) (q : ℕ) (horder : orderOf a = q) (i : ZMod q) :
    LinearMap.det
        (((halfTurnTwistedDihedralRepresentation a q horder) (.r i)).toLinearEquiv :
          Plane →ₗ[ℝ] Plane) = 1 := by
  simp [halfTurnTwistedDihedralRepresentation]

@[simp]
theorem halfTurnTwistedDihedralRepresentation_det_sr
    (a : Circle) (q : ℕ) (horder : orderOf a = q) (i : ZMod q) :
    LinearMap.det
        (((halfTurnTwistedDihedralRepresentation a q horder) (.sr i)).toLinearEquiv :
          Plane →ₗ[ℝ] Plane) = -1 := by
  simp only [halfTurnTwistedDihedralRepresentation]
  exact halfTurn_mul_axisReflection_mul_planeRotation_det _

/-- Canonical adjacent point generators for a faithful dihedral finite-coset model.  The two
determinant hypotheses say exactly that the `r` and `sr` coordinates are the positive and
reversing cosets. -/
def finiteCosetDihedralGenerators {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1) :
    DihedralGenerators (finiteCosetPlaneGroup D) where
  rotation := ⟨finiteCosetPointElement D (.r 1), by
    change 0 < ((pointGroupDet (finiteCosetPlaneGroup D)
      (finiteCosetPointElement D (.r 1)) : ℝˣ) : ℝ)
    rw [pointGroupDet_apply, finiteCosetPointElement_coe, hrdet]
    norm_num⟩
  reflection := finiteCosetPointElement D (.sr 0)
  reflection_reversing := by
    intro hs
    have hpos := orientationPreserving_det_pos (finiteCosetPlaneGroup D)
      ⟨finiteCosetPointElement D (.sr 0), hs⟩
    rw [finiteCosetPointElement_coe, hsdet] at hpos
    norm_num at hpos
  rotation_generates := by
    intro r
    have hrange : (r.1 : Plane ≃ₗᵢ[ℝ] Plane) ∈ D.linearRep.range := by
      rw [← finiteCosetPlaneGroup_pointGroup D]
      exact r.1.property
    obtain ⟨p, hp⟩ := hrange
    cases p with
    | r i =>
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨k, ?_⟩
        apply Subtype.ext
        change (finiteCosetPointElement D (.r 1)) ^ k = r.1
        calc
          (finiteCosetPointElement D (.r 1)) ^ k =
              finiteCosetPointElement D (.r (k : ZMod q)) := by
            apply Subtype.ext
            change D.linearRep (.r 1) ^ k = D.linearRep (.r (k : ZMod q))
            rw [← map_zpow, DihedralGroup.r_one_zpow]
          _ = r.1 := by
            apply Subtype.ext
            exact hp
    | sr i =>
        have hpos := orientationPreserving_det_pos (finiteCosetPlaneGroup D) r
        have hdet : LinearMap.det
            (((r.1 : pointGroup (finiteCosetPlaneGroup D).carrier) :
              Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1 := by
          rw [← hp]
          exact hsdet i
        rw [hdet] at hpos
        norm_num at hpos
  rotation_ne_one := by
    intro h
    have hpoint : finiteCosetPointElement D (.r 1) = 1 :=
      congrArg Subtype.val h
    have hmodelOrder : orderOf (finiteCosetPointElement D (.r 1)) = order.toNat := by
      calc
        orderOf (finiteCosetPointElement D (.r 1)) =
            orderOf (D.linearRep (.r 1)) :=
          (orderOf_injective
            (pointGroup (finiteCosetPlaneGroup D).carrier).subtype
            Subtype.coe_injective (finiteCosetPointElement D (.r 1))).symm
        _ = orderOf (.r 1 : DihedralGroup q) :=
          orderOf_injective D.linearRep D.linearRep_injective _
        _ = q := DihedralGroup.orderOf_r_one
        _ = order.toNat := horder
    have hone : orderOf (finiteCosetPointElement D (.r 1)) = 1 := by
      rw [hpoint, orderOf_one]
    rw [hone] at hmodelOrder
    cases order <;> norm_num [DihedralRotationOrder.toNat] at hmodelOrder
  order := order
  rotation_order := by
    calc
      orderOf (finiteCosetPointElement D (.r 1)) =
          orderOf (D.linearRep (.r 1)) :=
        (orderOf_injective
          (pointGroup (finiteCosetPlaneGroup D).carrier).subtype
          Subtype.coe_injective (finiteCosetPointElement D (.r 1))).symm
      _ = orderOf (.r 1 : DihedralGroup q) :=
        orderOf_injective D.linearRep D.linearRep_injective _
      _ = q := DihedralGroup.orderOf_r_one
      _ = order.toNat := horder

@[simp]
theorem finiteCosetDihedralGenerators_rotation {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1) :
    (finiteCosetDihedralGenerators D order horder hrdet hsdet).rotation.1 =
      finiteCosetPointElement D (.r 1) :=
  rfl

@[simp]
theorem finiteCosetDihedralGenerators_reflection {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1) :
    (finiteCosetDihedralGenerators D order horder hrdet hsdet).reflection =
      finiteCosetPointElement D (.sr 0) :=
  rfl

@[simp]
theorem finiteCosetDihedralGenerators_secondReflection {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1) :
    (finiteCosetDihedralGenerators D order horder hrdet hsdet).secondReflection =
      finiteCosetPointElement D (.sr 1) := by
  rw [DihedralGenerators.secondReflection,
    finiteCosetDihedralGenerators_reflection,
    finiteCosetDihedralGenerators_rotation, ← finiteCosetPointElement_mul]
  congr
  simp

@[simp]
theorem finiteCosetDihedralGenerators_rotation_action_coe {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1)
    (t : (finiteCosetPlaneGroup D).translationLattice.carrier) :
    ((finiteCosetPlaneGroup D).latticeAction
        (finiteCosetDihedralGenerators D order horder hrdet hsdet).rotation.1 t : Plane) =
      D.linearRep (.r 1) (t : Plane) := by
  rw [finiteCosetDihedralGenerators_rotation,
    PlaneGroup.latticeAction_coe, finiteCosetPointElement_coe]

@[simp]
theorem finiteCosetDihedralGenerators_reflection_action_coe {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1)
    (t : (finiteCosetPlaneGroup D).translationLattice.carrier) :
    ((finiteCosetPlaneGroup D).latticeAction
        (finiteCosetDihedralGenerators D order horder hrdet hsdet).reflection t : Plane) =
      D.linearRep (.sr 0) (t : Plane) := by
  rw [finiteCosetDihedralGenerators_reflection,
    PlaneGroup.latticeAction_coe, finiteCosetPointElement_coe]

/-- The affine representatives of `sr 0` and `sr 1` give canonical adjacent-reflection lift
data for every finite-coset dihedral model. -/
def finiteCosetTwoReflectionExtensionData {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1) :
    TwoReflectionExtensionData (finiteCosetPlaneGroup D)
      (finiteCosetDihedralGenerators D order horder hrdet hsdet) where
  firstLift := finiteCosetLift D (.sr 0)
  first_projection := by
    rw [finiteCosetLift_projection,
      finiteCosetDihedralGenerators_reflection]
  secondLift := finiteCosetLift D (.sr 1)
  second_projection := by
    rw [finiteCosetLift_projection,
      finiteCosetDihedralGenerators_secondReflection]

/-- Canonical adjacent point generators for the primitive rectangular model. -/
def pmmDihedralGenerators : DihedralGenerators pmmModel :=
  finiteCosetDihedralGenerators pmmCosetData .two rfl
    (by intro i; simp [pmmCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [pmmCosetData, symmorphicDihedralCosetData])

/-- Canonical adjacent point generators for the centered rectangular model. -/
def cmmDihedralGenerators : DihedralGenerators cmmModel :=
  finiteCosetDihedralGenerators cmmCosetData .two rfl
    (by intro i; simp [cmmCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [cmmCosetData, symmorphicDihedralCosetData])

/-- Canonical adjacent point generators for `pmg`. -/
def pmgDihedralGenerators : DihedralGenerators pmgModel :=
  finiteCosetDihedralGenerators pmgCosetData .two rfl
    (by intro i; simp [pmgCosetData, pmmCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [pmgCosetData, pmmCosetData, symmorphicDihedralCosetData])

/-- Canonical adjacent point generators for `pgg`. -/
def pggDihedralGenerators : DihedralGenerators pggModel :=
  finiteCosetDihedralGenerators pggCosetData .two rfl
    (by intro i; simp [pggCosetData, pmmCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [pggCosetData, pmmCosetData, symmorphicDihedralCosetData])

/-- Canonical adjacent point generators for the full-axis-span triangular model. -/
def p3m1DihedralGenerators : DihedralGenerators p3m1Model :=
  finiteCosetDihedralGenerators p3m1CosetData .three rfl
    (by intro i; simp [p3m1CosetData, symmorphicDihedralCosetData])
    (by intro i; simp [p3m1CosetData, symmorphicDihedralCosetData])

/-- Canonical adjacent point generators for the index-three triangular model. -/
def p31mDihedralGenerators : DihedralGenerators p31mModel :=
  finiteCosetDihedralGenerators p31mCosetData .three rfl
    (by intro i; simp [p31mCosetData, twistedSymmorphicDihedralCosetData])
    (by intro i; simp [p31mCosetData, twistedSymmorphicDihedralCosetData])

/-- Canonical adjacent point generators for the symmorphic square model. -/
def p4mDihedralGenerators : DihedralGenerators p4mModel :=
  finiteCosetDihedralGenerators p4mCosetData .four rfl
    (by intro i; simp [p4mCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [p4mCosetData, symmorphicDihedralCosetData])

/-- Canonical adjacent point generators for the square glide model. -/
def p4gDihedralGenerators : DihedralGenerators p4gModel :=
  finiteCosetDihedralGenerators p4gCosetData .four rfl
    (by intro i; simp [p4gCosetData, p4mCosetData,
      symmorphicDihedralCosetData])
    (by intro i; simp [p4gCosetData, p4mCosetData,
      symmorphicDihedralCosetData])

/-- Canonical adjacent point generators for the hexagonal model. -/
def p6mDihedralGenerators : DihedralGenerators p6mModel :=
  finiteCosetDihedralGenerators p6mCosetData .six rfl
    (by intro i; simp [p6mCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [p6mCosetData, symmorphicDihedralCosetData])

/-! ## Canonical adjacent affine lifts -/

def pmmTwoReflectionData :
    TwoReflectionExtensionData pmmModel pmmDihedralGenerators :=
  finiteCosetTwoReflectionExtensionData pmmCosetData .two rfl
    (by intro i; simp [pmmCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [pmmCosetData, symmorphicDihedralCosetData])

def cmmTwoReflectionData :
    TwoReflectionExtensionData cmmModel cmmDihedralGenerators :=
  finiteCosetTwoReflectionExtensionData cmmCosetData .two rfl
    (by intro i; simp [cmmCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [cmmCosetData, symmorphicDihedralCosetData])

def pmgTwoReflectionData :
    TwoReflectionExtensionData pmgModel pmgDihedralGenerators :=
  finiteCosetTwoReflectionExtensionData pmgCosetData .two rfl
    (by intro i; simp [pmgCosetData, pmmCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [pmgCosetData, pmmCosetData, symmorphicDihedralCosetData])

def pggTwoReflectionData :
    TwoReflectionExtensionData pggModel pggDihedralGenerators :=
  finiteCosetTwoReflectionExtensionData pggCosetData .two rfl
    (by intro i; simp [pggCosetData, pmmCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [pggCosetData, pmmCosetData, symmorphicDihedralCosetData])

def p3m1TwoReflectionData :
    TwoReflectionExtensionData p3m1Model p3m1DihedralGenerators :=
  finiteCosetTwoReflectionExtensionData p3m1CosetData .three rfl
    (by intro i; simp [p3m1CosetData, symmorphicDihedralCosetData])
    (by intro i; simp [p3m1CosetData, symmorphicDihedralCosetData])

def p31mTwoReflectionData :
    TwoReflectionExtensionData p31mModel p31mDihedralGenerators :=
  finiteCosetTwoReflectionExtensionData p31mCosetData .three rfl
    (by intro i; simp [p31mCosetData, twistedSymmorphicDihedralCosetData])
    (by intro i; simp [p31mCosetData, twistedSymmorphicDihedralCosetData])

def p4mTwoReflectionData :
    TwoReflectionExtensionData p4mModel p4mDihedralGenerators :=
  finiteCosetTwoReflectionExtensionData p4mCosetData .four rfl
    (by intro i; simp [p4mCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [p4mCosetData, symmorphicDihedralCosetData])

def p4gTwoReflectionData :
    TwoReflectionExtensionData p4gModel p4gDihedralGenerators :=
  finiteCosetTwoReflectionExtensionData p4gCosetData .four rfl
    (by intro i; simp [p4gCosetData, p4mCosetData,
      symmorphicDihedralCosetData])
    (by intro i; simp [p4gCosetData, p4mCosetData,
      symmorphicDihedralCosetData])

def p6mTwoReflectionData :
    TwoReflectionExtensionData p6mModel p6mDihedralGenerators :=
  finiteCosetTwoReflectionExtensionData p6mCosetData .six rfl
    (by intro i; simp [p6mCosetData, symmorphicDihedralCosetData])
    (by intro i; simp [p6mCosetData, symmorphicDihedralCosetData])

/-- The `pmg` presentation after exchanging its two adjacent order-two reflection families. -/
def pmgSwappedDihedralGenerators : DihedralGenerators pmgModel :=
  pmgDihedralGenerators.rotateReflection 1

/-- In the swapped `pmg` presentation the glide family is first and the mirror family second. -/
def pmgSwappedTwoReflectionData :
    TwoReflectionExtensionData pmgModel pmgSwappedDihedralGenerators :=
  pmgTwoReflectionData.swapOrderTwo rfl

/-! ## Explicit simultaneous lattice normal forms -/

private theorem toMatrix_eq_fin_two_of_apply
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin 2) ℤ M) (f : M →ₗ[ℤ] M)
    (a00 a01 a10 a11 : ℤ)
    (h0 : f (b 0) = a00 • b 0 + a10 • b 1)
    (h1 : f (b 1) = a01 • b 0 + a11 • b 1) :
    LinearMap.toMatrix b b f = !![a00, a01; a10, a11] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, h0, h1]

@[simp]
theorem finiteCoset_latticeAction_coe {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P)
    (t : (finiteCosetPlaneGroup D).translationLattice.carrier) :
    ((finiteCosetPlaneGroup D).latticeAction (finiteCosetPointElement D p) t : Plane) =
      D.linearRep p (t : Plane) :=
  rfl

private theorem dihedralLinearRepresentation_r_one_eq
    (a : Circle) (q : ℕ) (horder : orderOf a = q) :
    dihedralLinearRepresentation a q horder (.r 1) = planeRotation a := by
  change planeRotation
      (Additive.toMul (circlePowerMod a q _ 1)) = planeRotation a
  apply congrArg planeRotation
  rw [show (1 : ZMod q) = ((1 : ℤ) : ZMod q) by norm_num,
    circlePowerMod_coe]
  simp

private theorem dihedralLinearRepresentation_sr_zero_eq
    (a : Circle) (q : ℕ) (horder : orderOf a = q) :
    dihedralLinearRepresentation a q horder (.sr 0) = axisReflection := by
  change axisReflection * planeRotation
    (Additive.toMul (circlePowerMod a q _ 0)) = axisReflection
  rw [circlePowerMod_zero, planeRotation_one, mul_one]

private theorem halfTurnTwistedDihedralRepresentation_sr_zero_eq
    (a : Circle) (q : ℕ) (horder : orderOf a = q) :
    halfTurnTwistedDihedralRepresentation a q horder (.sr 0) =
      planeRotation (squareRoot ^ 2) * axisReflection := by
  change planeRotation (squareRoot ^ 2) *
    dihedralLinearRepresentation a q horder (.sr 0) = _
  rw [dihedralLinearRepresentation_sr_zero_eq]

private theorem halfTurnTwistedDihedralRepresentation_r_one_eq
    (a : Circle) (q : ℕ) (horder : orderOf a = q) :
    halfTurnTwistedDihedralRepresentation a q horder (.r 1) =
      planeRotation a := by
  change dihedralLinearRepresentation a q horder (.r 1) = planeRotation a
  exact dihedralLinearRepresentation_r_one_eq a q horder

private theorem finiteCoset_latticeAction_toMatrix_eq_fin_two
    {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P)
    (b : Module.Basis (Fin 2) ℤ
      (finiteCosetPlaneGroup D).translationLattice.carrier)
    (a00 a01 a10 a11 : ℤ)
    (h0 : D.linearRep p (b 0 : Plane) =
      a00 • (b 0 : Plane) + a10 • (b 1 : Plane))
    (h1 : D.linearRep p (b 1 : Plane) =
      a01 • (b 0 : Plane) + a11 • (b 1 : Plane)) :
    LinearMap.toMatrix b b
        ((finiteCosetPlaneGroup D).latticeAction
          (finiteCosetPointElement D p)).toLinearMap =
      !![a00, a01; a10, a11] := by
  apply toMatrix_eq_fin_two_of_apply
  · apply Subtype.ext
    change
      (((finiteCosetPlaneGroup D).latticeAction
        (finiteCosetPointElement D p) (b 0) :
          (finiteCosetPlaneGroup D).translationLattice.carrier) : Plane) =
        a00 • (b 0 : Plane) + a10 • (b 1 : Plane)
    exact (finiteCoset_latticeAction_coe D p (b 0)).trans h0
  · apply Subtype.ext
    change
      (((finiteCosetPlaneGroup D).latticeAction
        (finiteCosetPointElement D p) (b 1) :
          (finiteCosetPlaneGroup D).translationLattice.carrier) : Plane) =
        a01 • (b 0 : Plane) + a11 • (b 1 : Plane)
    exact (finiteCoset_latticeAction_coe D p (b 1)).trans h1

private def finiteCosetDihedralNormalForm
    {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (L : RankTwoLattice Plane) (hlattice : D.lattice = L)
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1)
    (form : DihedralLatticeForm) (hform : form.order = order)
    (b : Module.Basis (Fin 2) ℤ L.carrier)
    (r00 r01 r10 r11 s00 s01 s10 s11 : ℤ)
    (hrotationMatrix : form.rotationMatrix = !![r00, r01; r10, r11])
    (hreflectionMatrix : form.reflectionMatrix = !![s00, s01; s10, s11])
    (hr0 : D.linearRep (.r 1) (b 0 : Plane) =
      r00 • (b 0 : Plane) + r10 • (b 1 : Plane))
    (hr1 : D.linearRep (.r 1) (b 1 : Plane) =
      r01 • (b 0 : Plane) + r11 • (b 1 : Plane))
    (hs0 : D.linearRep (.sr 0) (b 0 : Plane) =
      s00 • (b 0 : Plane) + s10 • (b 1 : Plane))
    (hs1 : D.linearRep (.sr 0) (b 1 : Plane) =
      s01 • (b 0 : Plane) + s11 • (b 1 : Plane)) :
    DihedralLatticeNormalForm (finiteCosetPlaneGroup D)
      (finiteCosetDihedralGenerators D order horder hrdet hsdet) := by
  subst L
  refine DihedralLatticeNormalForm.ofMatrices
    (finiteCosetPlaneGroup D)
    (finiteCosetDihedralGenerators D order horder hrdet hsdet)
    form hform b ?_ ?_
  · exact (finiteCoset_latticeAction_toMatrix_eq_fin_two
      (D := D) (p := .r 1) (b := b)
      r00 r01 r10 r11 hr0 hr1).trans hrotationMatrix.symm
  · exact (finiteCoset_latticeAction_toMatrix_eq_fin_two
      (D := D) (p := .sr 0) (b := b)
      s00 s01 s10 s11 hs0 hs1).trans hreflectionMatrix.symm

/-- The primitive rectangular simultaneous normal form used by `pmm`, `pmg`, and `pgg`. -/
def pmmDihedralNormalForm :
    DihedralLatticeNormalForm pmmModel pmmDihedralGenerators := by
  simpa only [pmmModel, pmmDihedralGenerators] using
    finiteCosetDihedralNormalForm
      pmmCosetData RankTwoLattice.standardLattice rfl .two rfl
      (by intro i; simp [pmmCosetData, symmorphicDihedralCosetData])
      (by intro i; simp [pmmCosetData, symmorphicDihedralCosetData])
      .orderTwoPrimitive rfl RankTwoLattice.standardLattice.basis
      (-1) 0 0 (-1) 1 0 0 (-1) rfl rfl
      (by
        rw [pmmCosetData_linearRep_r_one, halfTurn_apply]
        module)
      (by
        rw [pmmCosetData_linearRep_r_one, halfTurn_apply]
        module)
      (by
        rw [pmmCosetData_linearRep_sr_zero]
        change axisReflection squareBasisZero =
          (1 : ℤ) • squareBasisZero + 0 • squareBasisOne
        rw [axisReflection_squareBasisZero]
        module)
      (by
        rw [pmmCosetData_linearRep_sr_zero]
        change axisReflection squareBasisOne =
          (0 : ℤ) • squareBasisZero + (-1) • squareBasisOne
        rw [axisReflection_squareBasisOne]
        module)

def pmgDihedralNormalForm :
    DihedralLatticeNormalForm pmgModel pmgDihedralGenerators := by
  simpa only [pmgModel, pmgDihedralGenerators] using
    finiteCosetDihedralNormalForm
      pmgCosetData RankTwoLattice.standardLattice rfl .two rfl
      (by intro i; simp [pmgCosetData, pmmCosetData,
        symmorphicDihedralCosetData])
      (by intro i; simp [pmgCosetData, pmmCosetData,
        symmorphicDihedralCosetData])
      .orderTwoPrimitive rfl RankTwoLattice.standardLattice.basis
      (-1) 0 0 (-1) 1 0 0 (-1) rfl rfl
      (by
        change pmmCosetData.linearRep (.r 1) _ = _
        rw [pmmCosetData_linearRep_r_one, halfTurn_apply]
        module)
      (by
        change pmmCosetData.linearRep (.r 1) _ = _
        rw [pmmCosetData_linearRep_r_one, halfTurn_apply]
        module)
      (by
        change pmmCosetData.linearRep (.sr 0) _ = _
        rw [pmmCosetData_linearRep_sr_zero]
        change axisReflection squareBasisZero =
          (1 : ℤ) • squareBasisZero + 0 • squareBasisOne
        rw [axisReflection_squareBasisZero]
        module)
      (by
        change pmmCosetData.linearRep (.sr 0) _ = _
        rw [pmmCosetData_linearRep_sr_zero]
        change axisReflection squareBasisOne =
          (0 : ℤ) • squareBasisZero + (-1) • squareBasisOne
        rw [axisReflection_squareBasisOne]
        module)

def pggDihedralNormalForm :
    DihedralLatticeNormalForm pggModel pggDihedralGenerators := by
  simpa only [pggModel, pggDihedralGenerators] using
    finiteCosetDihedralNormalForm
      pggCosetData RankTwoLattice.standardLattice rfl .two rfl
      (by intro i; simp [pggCosetData, pmmCosetData,
        symmorphicDihedralCosetData])
      (by intro i; simp [pggCosetData, pmmCosetData,
        symmorphicDihedralCosetData])
      .orderTwoPrimitive rfl RankTwoLattice.standardLattice.basis
      (-1) 0 0 (-1) 1 0 0 (-1) rfl rfl
      (by
        change pmmCosetData.linearRep (.r 1) _ = _
        rw [pmmCosetData_linearRep_r_one, halfTurn_apply]
        module)
      (by
        change pmmCosetData.linearRep (.r 1) _ = _
        rw [pmmCosetData_linearRep_r_one, halfTurn_apply]
        module)
      (by
        change pmmCosetData.linearRep (.sr 0) _ = _
        rw [pmmCosetData_linearRep_sr_zero]
        change axisReflection squareBasisZero =
          (1 : ℤ) • squareBasisZero + 0 • squareBasisOne
        rw [axisReflection_squareBasisZero]
        module)
      (by
        change pmmCosetData.linearRep (.sr 0) _ = _
        rw [pmmCosetData_linearRep_sr_zero]
        change axisReflection squareBasisOne =
          (0 : ℤ) • squareBasisZero + (-1) • squareBasisOne
        rw [axisReflection_squareBasisOne]
        module)

def cmmDihedralNormalForm :
    DihedralLatticeNormalForm cmmModel cmmDihedralGenerators := by
  simpa only [cmmModel, cmmDihedralGenerators] using
    finiteCosetDihedralNormalForm
      cmmCosetData centeredLattice rfl .two rfl
      (by intro i; simp [cmmCosetData, symmorphicDihedralCosetData])
      (by intro i; simp [cmmCosetData, symmorphicDihedralCosetData])
      .orderTwoCentered rfl centeredLattice.basis
      (-1) 0 0 (-1) 1 1 0 (-1) rfl rfl
      (by
        rw [show cmmCosetData.linearRep (.r 1) =
            planeRotation (squareRoot ^ 2) by
          simpa only [cmmCosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_r_one_eq
              (squareRoot ^ 2) 2 squareRoot_sq_order,
          halfTurn_apply]
        module)
      (by
        rw [show cmmCosetData.linearRep (.r 1) =
            planeRotation (squareRoot ^ 2) by
          simpa only [cmmCosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_r_one_eq
              (squareRoot ^ 2) 2 squareRoot_sq_order,
          halfTurn_apply]
        module)
      (by
        rw [show cmmCosetData.linearRep (.sr 0) = axisReflection by
          simpa only [cmmCosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_sr_zero_eq
              (squareRoot ^ 2) 2 squareRoot_sq_order,
          axisReflection_centered_basis_zero]
        module)
      (by
        rw [show cmmCosetData.linearRep (.sr 0) = axisReflection by
          simpa only [cmmCosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_sr_zero_eq
              (squareRoot ^ 2) 2 squareRoot_sq_order,
          axisReflection_centered_basis_one]
        module)

def p4mDihedralNormalForm :
    DihedralLatticeNormalForm p4mModel p4mDihedralGenerators := by
  simpa only [p4mModel, p4mDihedralGenerators] using
    finiteCosetDihedralNormalForm
      p4mCosetData RankTwoLattice.standardLattice rfl .four rfl
      (by intro i; simp [p4mCosetData, symmorphicDihedralCosetData])
      (by intro i; simp [p4mCosetData, symmorphicDihedralCosetData])
      .orderFour rfl RankTwoLattice.standardLattice.basis
      0 (-1) 1 0 1 0 0 (-1) rfl rfl
      (by
        rw [p4mCosetData_linearRep_r_one]
        change planeRotation squareRoot squareBasisZero =
          (0 : ℤ) • squareBasisZero + 1 • squareBasisOne
        rw [squareQuarterTurn_basis_zero]
        module)
      (by
        rw [p4mCosetData_linearRep_r_one]
        change planeRotation squareRoot squareBasisOne =
          (-1 : ℤ) • squareBasisZero + 0 • squareBasisOne
        rw [squareQuarterTurn_basis_one]
        module)
      (by
        rw [p4mCosetData_linearRep_sr_zero]
        change axisReflection squareBasisZero =
          (1 : ℤ) • squareBasisZero + 0 • squareBasisOne
        rw [axisReflection_squareBasisZero]
        module)
      (by
        rw [p4mCosetData_linearRep_sr_zero]
        change axisReflection squareBasisOne =
          (0 : ℤ) • squareBasisZero + (-1) • squareBasisOne
        rw [axisReflection_squareBasisOne]
        module)

def p4gDihedralNormalForm :
    DihedralLatticeNormalForm p4gModel p4gDihedralGenerators := by
  simpa only [p4gModel, p4gDihedralGenerators] using
    finiteCosetDihedralNormalForm
      p4gCosetData RankTwoLattice.standardLattice rfl .four rfl
      (by intro i; simp [p4gCosetData, p4mCosetData,
        symmorphicDihedralCosetData])
      (by intro i; simp [p4gCosetData, p4mCosetData,
        symmorphicDihedralCosetData])
      .orderFour rfl RankTwoLattice.standardLattice.basis
      0 (-1) 1 0 1 0 0 (-1) rfl rfl
      (by
        change p4mCosetData.linearRep (.r 1) _ = _
        rw [p4mCosetData_linearRep_r_one]
        change planeRotation squareRoot squareBasisZero =
          (0 : ℤ) • squareBasisZero + 1 • squareBasisOne
        rw [squareQuarterTurn_basis_zero]
        module)
      (by
        change p4mCosetData.linearRep (.r 1) _ = _
        rw [p4mCosetData_linearRep_r_one]
        change planeRotation squareRoot squareBasisOne =
          (-1 : ℤ) • squareBasisZero + 0 • squareBasisOne
        rw [squareQuarterTurn_basis_one]
        module)
      (by
        change p4mCosetData.linearRep (.sr 0) _ = _
        rw [p4mCosetData_linearRep_sr_zero]
        change axisReflection squareBasisZero =
          (1 : ℤ) • squareBasisZero + 0 • squareBasisOne
        rw [axisReflection_squareBasisZero]
        module)
      (by
        change p4mCosetData.linearRep (.sr 0) _ = _
        rw [p4mCosetData_linearRep_sr_zero]
        change axisReflection squareBasisOne =
          (0 : ℤ) • squareBasisZero + (-1) • squareBasisOne
        rw [axisReflection_squareBasisOne]
        module)

theorem hexRotation_basis_zero_eq :
    planeRotation hexRoot (hexLattice.basis 0 : Plane) =
      (hexLattice.basis 1 : Plane) := by
  apply coordinateIsometry.injective
  simp

theorem hexRotation_basis_one_eq :
    planeRotation hexRoot (hexLattice.basis 1 : Plane) =
      (hexLattice.basis 1 : Plane) - (hexLattice.basis 0 : Plane) := by
  apply coordinateIsometry.injective
  simp
  linear_combination hexRoot_poly

theorem axisReflection_hex_basis_zero :
    axisReflection (hexLattice.basis 0 : Plane) =
      (hexLattice.basis 0 : Plane) := by
  apply coordinateIsometry.injective
  simp

theorem axisReflection_hex_basis_one :
    axisReflection (hexLattice.basis 1 : Plane) =
      (hexLattice.basis 0 : Plane) - (hexLattice.basis 1 : Plane) := by
  apply coordinateIsometry.injective
  rw [coordinateIsometry_axisReflection, coordinateIsometry_hexLattice_basis_one,
    map_sub, coordinateIsometry_hexLattice_basis_zero,
    coordinateIsometry_hexLattice_basis_one]
  change (starRingEnd ℂ) (hexRoot : ℂ) = 1 - (hexRoot : ℂ)
  rw [← Circle.coe_inv_eq_conj]
  exact hexRoot_coe_inv

def p6mDihedralNormalForm :
    DihedralLatticeNormalForm p6mModel p6mDihedralGenerators := by
  simpa only [p6mModel, p6mDihedralGenerators] using
    finiteCosetDihedralNormalForm
      p6mCosetData hexLattice rfl .six rfl
      (by intro i; simp [p6mCosetData, symmorphicDihedralCosetData])
      (by intro i; simp [p6mCosetData, symmorphicDihedralCosetData])
      .orderSix rfl hexLattice.basis
      0 (-1) 1 1 1 1 0 (-1) rfl rfl
      (by
        rw [show p6mCosetData.linearRep (.r 1) = planeRotation hexRoot by
          simpa only [p6mCosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_r_one_eq hexRoot 6 hexRoot_order,
          hexRotation_basis_zero_eq]
        module)
      (by
        rw [show p6mCosetData.linearRep (.r 1) = planeRotation hexRoot by
          simpa only [p6mCosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_r_one_eq hexRoot 6 hexRoot_order,
          hexRotation_basis_one_eq]
        module)
      (by
        rw [show p6mCosetData.linearRep (.sr 0) = axisReflection by
          simpa only [p6mCosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_sr_zero_eq hexRoot 6 hexRoot_order,
          axisReflection_hex_basis_zero]
        module)
      (by
        rw [show p6mCosetData.linearRep (.sr 0) = axisReflection by
          simpa only [p6mCosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_sr_zero_eq hexRoot 6 hexRoot_order,
          axisReflection_hex_basis_one]
        module)

/-- The unimodular shear `(b₀,b₁) ↦ (b₀,b₁-b₀)` used by both order-three
models. -/
def hexOrderThreeBasis : Module.Basis (Fin 2) ℤ hexLattice.carrier :=
  IntegralReflection.shearBasis hexLattice.basis (-1)

@[simp]
theorem hexOrderThreeBasis_zero :
    hexOrderThreeBasis 0 = hexLattice.basis 0 := by
  simp [hexOrderThreeBasis, IntegralReflection.shearBasis_zero]

@[simp]
theorem hexOrderThreeBasis_one :
    hexOrderThreeBasis 1 = hexLattice.basis 1 - hexLattice.basis 0 := by
  rw [hexOrderThreeBasis, IntegralReflection.shearBasis_one]
  module

theorem hexThirdTurn_orderThreeBasis_zero :
    planeRotation (hexRoot ^ 2) (hexOrderThreeBasis 0 : Plane) =
      (hexOrderThreeBasis 1 : Plane) := by
  rw [hexOrderThreeBasis_zero, hexOrderThreeBasis_one]
  change planeRotation (hexRoot ^ 2) (hexLattice.basis 0 : Plane) =
    (hexLattice.basis 1 : Plane) - (hexLattice.basis 0 : Plane)
  rw [pow_two, planeRotation_mul]
  change planeRotation hexRoot
      (planeRotation hexRoot (hexLattice.basis 0 : Plane)) = _
  rw [hexRotation_basis_zero_eq, hexRotation_basis_one_eq]

theorem hexThirdTurn_orderThreeBasis_one :
    planeRotation (hexRoot ^ 2) (hexOrderThreeBasis 1 : Plane) =
      -(hexOrderThreeBasis 0 : Plane) - (hexOrderThreeBasis 1 : Plane) := by
  rw [hexOrderThreeBasis_zero, hexOrderThreeBasis_one]
  change planeRotation (hexRoot ^ 2)
      ((hexLattice.basis 1 : Plane) - (hexLattice.basis 0 : Plane)) =
    -(hexLattice.basis 0 : Plane) -
      ((hexLattice.basis 1 : Plane) - (hexLattice.basis 0 : Plane))
  rw [map_sub, pow_two, planeRotation_mul]
  change planeRotation hexRoot
        (planeRotation hexRoot (hexLattice.basis 1 : Plane)) -
      planeRotation hexRoot
        (planeRotation hexRoot (hexLattice.basis 0 : Plane)) = _
  rw [hexRotation_basis_one_eq, hexRotation_basis_zero_eq, map_sub,
    hexRotation_basis_one_eq, hexRotation_basis_zero_eq]
  module

theorem axisReflection_orderThreeBasis_zero :
    axisReflection (hexOrderThreeBasis 0 : Plane) =
      (hexOrderThreeBasis 0 : Plane) := by
  rw [hexOrderThreeBasis_zero, axisReflection_hex_basis_zero]

theorem axisReflection_orderThreeBasis_one :
    axisReflection (hexOrderThreeBasis 1 : Plane) =
      -(hexOrderThreeBasis 0 : Plane) - (hexOrderThreeBasis 1 : Plane) := by
  rw [hexOrderThreeBasis_zero, hexOrderThreeBasis_one]
  change axisReflection
      ((hexLattice.basis 1 : Plane) - (hexLattice.basis 0 : Plane)) =
    -(hexLattice.basis 0 : Plane) -
      ((hexLattice.basis 1 : Plane) - (hexLattice.basis 0 : Plane))
  rw [map_sub, axisReflection_hex_basis_one, axisReflection_hex_basis_zero]
  module

def p3m1DihedralNormalForm :
    DihedralLatticeNormalForm p3m1Model p3m1DihedralGenerators := by
  simpa only [p3m1Model, p3m1DihedralGenerators] using
    finiteCosetDihedralNormalForm
      p3m1CosetData hexLattice rfl .three rfl
      (by intro i; simp [p3m1CosetData, symmorphicDihedralCosetData])
      (by intro i; simp [p3m1CosetData, symmorphicDihedralCosetData])
      .p3m1 rfl hexOrderThreeBasis
      0 (-1) 1 (-1) 1 (-1) 0 (-1) rfl rfl
      (by
        rw [show p3m1CosetData.linearRep (.r 1) =
            planeRotation (hexRoot ^ 2) by
          simpa only [p3m1CosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_r_one_eq
              (hexRoot ^ 2) 3 hexRoot_sq_order,
          hexThirdTurn_orderThreeBasis_zero]
        module)
      (by
        rw [show p3m1CosetData.linearRep (.r 1) =
            planeRotation (hexRoot ^ 2) by
          simpa only [p3m1CosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_r_one_eq
              (hexRoot ^ 2) 3 hexRoot_sq_order,
          hexThirdTurn_orderThreeBasis_one]
        module)
      (by
        rw [show p3m1CosetData.linearRep (.sr 0) = axisReflection by
          simpa only [p3m1CosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_sr_zero_eq
              (hexRoot ^ 2) 3 hexRoot_sq_order,
          axisReflection_orderThreeBasis_zero]
        module)
      (by
        rw [show p3m1CosetData.linearRep (.sr 0) = axisReflection by
          simpa only [p3m1CosetData, symmorphicDihedralCosetData] using
            dihedralLinearRepresentation_sr_zero_eq
              (hexRoot ^ 2) 3 hexRoot_sq_order,
          axisReflection_orderThreeBasis_one]
        module)

private theorem halfTurnAxis_orderThreeBasis_zero :
    (planeRotation (squareRoot ^ 2) * axisReflection)
        (hexOrderThreeBasis 0 : Plane) =
      -(hexOrderThreeBasis 0 : Plane) := by
  calc
    _ = planeRotation (squareRoot ^ 2)
        (axisReflection (hexOrderThreeBasis 0 : Plane)) := rfl
    _ = planeRotation (squareRoot ^ 2) (hexOrderThreeBasis 0 : Plane) :=
      congrArg (planeRotation (squareRoot ^ 2))
        axisReflection_orderThreeBasis_zero
    _ = _ := halfTurn_apply _

private theorem halfTurnAxis_orderThreeBasis_one :
    (planeRotation (squareRoot ^ 2) * axisReflection)
        (hexOrderThreeBasis 1 : Plane) =
      (hexOrderThreeBasis 0 : Plane) + (hexOrderThreeBasis 1 : Plane) := by
  calc
    _ = planeRotation (squareRoot ^ 2)
        (axisReflection (hexOrderThreeBasis 1 : Plane)) := rfl
    _ = planeRotation (squareRoot ^ 2)
        (-(hexOrderThreeBasis 0 : Plane) -
          (hexOrderThreeBasis 1 : Plane)) :=
      congrArg (planeRotation (squareRoot ^ 2))
        axisReflection_orderThreeBasis_one
    _ = -(-(hexOrderThreeBasis 0 : Plane) -
        (hexOrderThreeBasis 1 : Plane)) := halfTurn_apply _
    _ = _ := by module

private theorem p31m_reflectionMatrix_eq :
    DihedralLatticeForm.p31m.reflectionMatrix = !![-1, 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DihedralLatticeForm.reflectionMatrix,
      dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full]

def p31mDihedralNormalForm :
    DihedralLatticeNormalForm p31mModel p31mDihedralGenerators := by
  simpa only [p31mModel, p31mDihedralGenerators] using
    finiteCosetDihedralNormalForm
      p31mCosetData hexLattice rfl .three rfl
      (by intro i; simp [p31mCosetData, twistedSymmorphicDihedralCosetData])
      (by intro i; simp [p31mCosetData, twistedSymmorphicDihedralCosetData])
      .p31m rfl hexOrderThreeBasis
      0 (-1) 1 (-1) (-1) 1 0 1 rfl p31m_reflectionMatrix_eq
      (by
        rw [show p31mCosetData.linearRep (.r 1) =
            planeRotation (hexRoot ^ 2) by
          simpa only [p31mCosetData, twistedSymmorphicDihedralCosetData] using
            halfTurnTwistedDihedralRepresentation_r_one_eq
              (hexRoot ^ 2) 3 hexRoot_sq_order,
          hexThirdTurn_orderThreeBasis_zero]
        module)
      (by
        rw [show p31mCosetData.linearRep (.r 1) =
            planeRotation (hexRoot ^ 2) by
          simpa only [p31mCosetData, twistedSymmorphicDihedralCosetData] using
            halfTurnTwistedDihedralRepresentation_r_one_eq
              (hexRoot ^ 2) 3 hexRoot_sq_order,
          hexThirdTurn_orderThreeBasis_one]
        module)
      (by
        rw [show p31mCosetData.linearRep (.sr 0) =
            planeRotation (squareRoot ^ 2) * axisReflection by
          simpa only [p31mCosetData, twistedSymmorphicDihedralCosetData] using
            halfTurnTwistedDihedralRepresentation_sr_zero_eq
              (hexRoot ^ 2) 3 hexRoot_sq_order,
          halfTurnAxis_orderThreeBasis_zero]
        module)
      (by
        rw [show p31mCosetData.linearRep (.sr 0) =
            planeRotation (squareRoot ^ 2) * axisReflection by
          simpa only [p31mCosetData, twistedSymmorphicDihedralCosetData] using
            halfTurnTwistedDihedralRepresentation_sr_zero_eq
              (hexRoot ^ 2) 3 hexRoot_sq_order,
          halfTurnAxis_orderThreeBasis_one]
        module)

/-! ## Quotient-valued shift status of the canonical adjacent lifts -/

private theorem finiteCosetLift_sq_translationPart
    {P : Type*} [Group P] [Finite P]
    (D : FiniteCosetData P) (p : P) :
    translationPart
        (((finiteCosetLift D p : (finiteCosetPlaneGroup D).carrier) :
          EuclideanMotion Plane) ^ 2) =
      D.shift p + D.linearRep p (D.shift p) := by
  change translationPart ((finiteCosetRepresentative D p) ^ 2) = _
  rw [pow_two, translationPart_mul]
  have ht : translationPart (finiteCosetRepresentative D p) = D.shift p := by
    simp [finiteCosetRepresentative, translationPart_mul]
  have hl : linearPart (finiteCosetRepresentative D p) = D.linearRep p := by
    simp only [finiteCosetRepresentative, linearPart_mul,
      linearPart_translation, linearPart_pureLinear, one_mul]
  rw [ht, hl]

private theorem TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
    {G : PlaneGroup} {d : DihedralGenerators G}
    (c : TwoReflectionExtensionData G d)
    (hzero : translationPart ((c.firstLift : EuclideanMotion Plane) ^ 2) = 0) :
    c.firstShiftClass = 0 := by
  rw [TwoReflectionExtensionData.firstShiftClass, shiftClass_eq_zero_iff]
  refine ⟨0, ?_⟩
  apply Subtype.ext
  change finiteNormHom G d.reflection 2 0 =
    liftPowerTranslation G d.reflection 2 d.reflection_sq
      c.firstLift c.first_projection
  simp only [map_zero]
  apply Subtype.ext
  exact hzero.symm

private theorem TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
    {G : PlaneGroup} {d : DihedralGenerators G}
    (c : TwoReflectionExtensionData G d)
    (hzero : translationPart ((c.secondLift : EuclideanMotion Plane) ^ 2) = 0) :
    c.secondShiftClass = 0 := by
  rw [TwoReflectionExtensionData.secondShiftClass, shiftClass_eq_zero_iff]
  refine ⟨0, ?_⟩
  apply Subtype.ext
  change finiteNormHom G d.secondReflection 2 0 =
    liftPowerTranslation G d.secondReflection 2 d.secondReflection_sq
      c.secondLift c.second_projection
  simp only [map_zero]
  apply Subtype.ext
  exact hzero.symm

private theorem TwoReflectionExtensionData.firstShiftClass_ne_zero_of_sq_translationPart
    {G : PlaneGroup} {d : DihedralGenerators G}
    (N : DihedralLatticeNormalForm G d)
    (c : TwoReflectionExtensionData G d)
    (hmatrix : N.form.reflectionMatrix =
      IntegralReflection.reflectionLatticeMatrix .primitive)
    (hbasis : translationPart ((c.firstLift : EuclideanMotion Plane) ^ 2) =
      (N.basis 0 : Plane)) :
    c.firstShiftClass ≠ 0 := by
  let R : G.ReflectionLatticeNormalForm d.reflection :=
    { kind := .primitive
      basis := N.basis
      matrix_eq := N.reflection_matrix_eq.trans hmatrix }
  intro hz
  have hmem := (shiftClass_eq_zero_iff G d.reflection 2 d.reflection_sq
    c.firstLift c.first_projection).mp hz
  rcases hmem with ⟨u, hu⟩
  apply R.primitive_basis_zero_not_mem_reflectionNormRange rfl
  rw [PlaneGroup.mem_reflectionNormRange_iff]
  let uL : G.translationLattice.carrier := G.latticeTranslationEquiv.symm u
  refine ⟨uL, ?_⟩
  apply G.latticeTranslationEquiv.injective
  change u + pointAction G.carrier d.reflection u =
    G.latticeTranslationEquiv (N.basis 0)
  have huv := congrArg Subtype.val hu
  change finiteNormHom G d.reflection 2 u =
    liftPowerTranslation G d.reflection 2 d.reflection_sq
      c.firstLift c.first_projection at huv
  rw [reflectionFiniteNormHom_two] at huv
  have hlift : liftPowerTranslation G d.reflection 2 d.reflection_sq
      c.firstLift c.first_projection = G.latticeTranslationEquiv (N.basis 0) := by
    apply Subtype.ext
    exact hbasis
  rw [hlift] at huv
  exact huv

private theorem symmorphicFirstShiftClass_eq_zero
    {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1)
    (hshift : D.shift (.sr 0) = 0) :
    (finiteCosetTwoReflectionExtensionData D order horder hrdet hsdet).firstShiftClass =
      0 := by
  apply TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
  change translationPart
      (((finiteCosetLift D (.sr 0) : (finiteCosetPlaneGroup D).carrier) :
        EuclideanMotion Plane) ^ 2) = 0
  rw [finiteCosetLift_sq_translationPart, hshift, map_zero, zero_add]

private theorem symmorphicSecondShiftClass_eq_zero
    {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1)
    (hshift : D.shift (.sr 1) = 0) :
    (finiteCosetTwoReflectionExtensionData D order horder hrdet hsdet).secondShiftClass =
      0 := by
  apply TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
  change translationPart
      (((finiteCosetLift D (.sr 1) : (finiteCosetPlaneGroup D).carrier) :
        EuclideanMotion Plane) ^ 2) = 0
  rw [finiteCosetLift_sq_translationPart, hshift, map_zero, zero_add]

private theorem symmorphicShiftClasses_eq_zero
    {q : ℕ} [NeZero q]
    (D : FiniteCosetData (DihedralGroup q))
    (order : DihedralRotationOrder) (horder : q = order.toNat)
    (hrdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.r i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hsdet : ∀ i : ZMod q,
      LinearMap.det
          ((D.linearRep (.sr i)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = -1)
    (hfirst : D.shift (.sr 0) = 0)
    (hsecond : D.shift (.sr 1) = 0) :
    (finiteCosetTwoReflectionExtensionData D order horder hrdet hsdet).firstShiftClass =
        0 ∧
      (finiteCosetTwoReflectionExtensionData D order horder hrdet hsdet).secondShiftClass =
        0 :=
  ⟨symmorphicFirstShiftClass_eq_zero D order horder hrdet hsdet hfirst,
    symmorphicSecondShiftClass_eq_zero D order horder hrdet hsdet hsecond⟩

private theorem pmmTwoReflectionData_shiftClasses_eq_zero :
    pmmTwoReflectionData.firstShiftClass = 0 ∧
      pmmTwoReflectionData.secondShiftClass = 0 := by
  constructor
  · apply TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift pmmCosetData (.sr 0) : pmmModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [pmmCosetData, symmorphicDihedralCosetData]
  · apply TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift pmmCosetData (.sr 1) : pmmModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [pmmCosetData, symmorphicDihedralCosetData]

/-- Both canonical adjacent lifts of `pmm` are mirrors. -/
theorem pmmTwoReflectionData_firstShiftClass_eq_zero :
    pmmTwoReflectionData.firstShiftClass = 0 :=
  pmmTwoReflectionData_shiftClasses_eq_zero.1

/-- Both canonical adjacent lifts of `pmm` are mirrors. -/
theorem pmmTwoReflectionData_secondShiftClass_eq_zero :
    pmmTwoReflectionData.secondShiftClass = 0 :=
  pmmTwoReflectionData_shiftClasses_eq_zero.2

private theorem cmmTwoReflectionData_shiftClasses_eq_zero :
    cmmTwoReflectionData.firstShiftClass = 0 ∧
      cmmTwoReflectionData.secondShiftClass = 0 := by
  constructor
  · apply TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift cmmCosetData (.sr 0) : cmmModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [cmmCosetData, symmorphicDihedralCosetData]
  · apply TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift cmmCosetData (.sr 1) : cmmModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [cmmCosetData, symmorphicDihedralCosetData]

/-- Both canonical adjacent lifts of `cmm` are mirrors. -/
theorem cmmTwoReflectionData_firstShiftClass_eq_zero :
    cmmTwoReflectionData.firstShiftClass = 0 :=
  cmmTwoReflectionData_shiftClasses_eq_zero.1

/-- Both canonical adjacent lifts of `cmm` are mirrors. -/
theorem cmmTwoReflectionData_secondShiftClass_eq_zero :
    cmmTwoReflectionData.secondShiftClass = 0 :=
  cmmTwoReflectionData_shiftClasses_eq_zero.2

private theorem p3m1TwoReflectionData_shiftClasses_eq_zero :
    p3m1TwoReflectionData.firstShiftClass = 0 ∧
      p3m1TwoReflectionData.secondShiftClass = 0 := by
  constructor
  · apply TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift p3m1CosetData (.sr 0) : p3m1Model.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [p3m1CosetData, symmorphicDihedralCosetData]
  · apply TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift p3m1CosetData (.sr 1) : p3m1Model.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [p3m1CosetData, symmorphicDihedralCosetData]

/-- Both canonical adjacent lifts of `p3m1` are mirrors. -/
theorem p3m1TwoReflectionData_firstShiftClass_eq_zero :
    p3m1TwoReflectionData.firstShiftClass = 0 :=
  p3m1TwoReflectionData_shiftClasses_eq_zero.1

/-- Both canonical adjacent lifts of `p3m1` are mirrors. -/
theorem p3m1TwoReflectionData_secondShiftClass_eq_zero :
    p3m1TwoReflectionData.secondShiftClass = 0 :=
  p3m1TwoReflectionData_shiftClasses_eq_zero.2

private theorem p31mTwoReflectionData_shiftClasses_eq_zero :
    p31mTwoReflectionData.firstShiftClass = 0 ∧
      p31mTwoReflectionData.secondShiftClass = 0 := by
  constructor
  · apply TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift p31mCosetData (.sr 0) : p31mModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [p31mCosetData, twistedSymmorphicDihedralCosetData]
  · apply TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift p31mCosetData (.sr 1) : p31mModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [p31mCosetData, twistedSymmorphicDihedralCosetData]

/-- Both canonical adjacent lifts of `p31m` are mirrors. -/
theorem p31mTwoReflectionData_firstShiftClass_eq_zero :
    p31mTwoReflectionData.firstShiftClass = 0 :=
  p31mTwoReflectionData_shiftClasses_eq_zero.1

/-- Both canonical adjacent lifts of `p31m` are mirrors. -/
theorem p31mTwoReflectionData_secondShiftClass_eq_zero :
    p31mTwoReflectionData.secondShiftClass = 0 :=
  p31mTwoReflectionData_shiftClasses_eq_zero.2

private theorem p4mTwoReflectionData_shiftClasses_eq_zero :
    p4mTwoReflectionData.firstShiftClass = 0 ∧
      p4mTwoReflectionData.secondShiftClass = 0 := by
  constructor
  · apply TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift p4mCosetData (.sr 0) : p4mModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [p4mCosetData, symmorphicDihedralCosetData]
  · apply TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift p4mCosetData (.sr 1) : p4mModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [p4mCosetData, symmorphicDihedralCosetData]

/-- Both canonical adjacent lifts of `p4m` are mirrors. -/
theorem p4mTwoReflectionData_firstShiftClass_eq_zero :
    p4mTwoReflectionData.firstShiftClass = 0 :=
  p4mTwoReflectionData_shiftClasses_eq_zero.1

/-- Both canonical adjacent lifts of `p4m` are mirrors. -/
theorem p4mTwoReflectionData_secondShiftClass_eq_zero :
    p4mTwoReflectionData.secondShiftClass = 0 :=
  p4mTwoReflectionData_shiftClasses_eq_zero.2

private theorem p6mTwoReflectionData_shiftClasses_eq_zero :
    p6mTwoReflectionData.firstShiftClass = 0 ∧
      p6mTwoReflectionData.secondShiftClass = 0 := by
  constructor
  · apply TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift p6mCosetData (.sr 0) : p6mModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [p6mCosetData, symmorphicDihedralCosetData]
  · apply TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
    change translationPart
        (((finiteCosetLift p6mCosetData (.sr 1) : p6mModel.carrier) :
          EuclideanMotion Plane) ^ 2) = 0
    rw [finiteCosetLift_sq_translationPart]
    simp [p6mCosetData, symmorphicDihedralCosetData]

/-- Both canonical adjacent lifts of `p6m` are mirrors. -/
theorem p6mTwoReflectionData_firstShiftClass_eq_zero :
    p6mTwoReflectionData.firstShiftClass = 0 :=
  p6mTwoReflectionData_shiftClasses_eq_zero.1

/-- Both canonical adjacent lifts of `p6m` are mirrors. -/
theorem p6mTwoReflectionData_secondShiftClass_eq_zero :
    p6mTwoReflectionData.secondShiftClass = 0 :=
  p6mTwoReflectionData_shiftClasses_eq_zero.2

/-- The first canonical `pmg` family is a mirror family. -/
theorem pmgTwoReflectionData_firstShiftClass_eq_zero :
    pmgTwoReflectionData.firstShiftClass = 0 := by
  apply TwoReflectionExtensionData.firstShiftClass_eq_zero_of_sq_translationPart
  change translationPart
      (((finiteCosetLift pmgCosetData (.sr 0) : pmgModel.carrier) :
        EuclideanMotion Plane) ^ 2) = 0
  rw [finiteCosetLift_sq_translationPart]
  change pmgShift (.sr 0) +
      pmmCosetData.linearRep (.sr 0) (pmgShift (.sr 0)) = 0
  rw [pmgShift_sr_zero, map_zero, zero_add]

/-- The primitive normal form after exchanging the two adjacent `pmg` reflection families. -/
def pmgSwappedDihedralNormalForm :
    DihedralLatticeNormalForm pmgModel pmgSwappedDihedralGenerators :=
  pmgDihedralNormalForm.swapOrderTwoPrimitive rfl

private theorem pmgSwappedTwoReflectionData_firstShiftClass_ne_zero :
    pmgSwappedTwoReflectionData.firstShiftClass ≠ 0 := by
  apply TwoReflectionExtensionData.firstShiftClass_ne_zero_of_sq_translationPart
    pmgSwappedDihedralNormalForm pmgSwappedTwoReflectionData
  · rfl
  · change translationPart
        (((finiteCosetLift pmgCosetData (.sr 1) : pmgModel.carrier) :
          EuclideanMotion Plane) ^ 2) =
        (pmgSwappedDihedralNormalForm.basis 0 : Plane)
    rw [finiteCosetLift_sq_translationPart]
    change pmgShift (.sr 1) +
        pmmCosetData.linearRep (.sr 1) (pmgShift (.sr 1)) = _
    rw [show (pmgSwappedDihedralNormalForm.basis 0 : Plane) = squareBasisOne by
      change
        ((pmgDihedralNormalForm.swappedBasis 0 :
          pmgModel.translationLattice.carrier) : Plane) = _
      rw [DihedralLatticeNormalForm.swappedBasis, Module.Basis.reindex_apply]
      change (pmgDihedralNormalForm.basis 1 : Plane) = _
      rfl,
      pmgShift_sr_one, map_smul, pmmLinear_sr_one_squareBasisOne]
    module

/-- The second canonical `pmg` family has nonzero quotient-valued glide class. -/
theorem pmgTwoReflectionData_secondShiftClass_ne_zero :
    pmgTwoReflectionData.secondShiftClass ≠ 0 := by
  intro hzero
  apply pmgSwappedTwoReflectionData_firstShiftClass_ne_zero
  change (pmgTwoReflectionData.swapOrderTwo rfl).firstShiftClass = 0
  exact (TwoReflectionExtensionData.swapOrderTwo_firstShiftClass_eq_zero_iff
    pmgTwoReflectionData rfl).2 hzero

/-- The first canonical `pgg` family has nonzero quotient-valued glide class. -/
theorem pggTwoReflectionData_firstShiftClass_ne_zero :
    pggTwoReflectionData.firstShiftClass ≠ 0 := by
  apply TwoReflectionExtensionData.firstShiftClass_ne_zero_of_sq_translationPart
    pggDihedralNormalForm pggTwoReflectionData
  · rfl
  · change translationPart
        (((finiteCosetLift pggCosetData (.sr 0) : pggModel.carrier) :
          EuclideanMotion Plane) ^ 2) =
        (pggDihedralNormalForm.basis 0 : Plane)
    rw [finiteCosetLift_sq_translationPart]
    change pggShift (.sr 0) +
        pmmCosetData.linearRep (.sr 0) (pggShift (.sr 0)) = _
    rw [show (pggDihedralNormalForm.basis 0 : Plane) = squareBasisZero by rfl,
      pggShift_sr_zero, map_smul, pmmLinear_sr_zero_squareBasisZero]
    module

private def pggSwappedDihedralGenerators : DihedralGenerators pggModel :=
  pggDihedralGenerators.rotateReflection 1

private def pggSwappedTwoReflectionData :
    TwoReflectionExtensionData pggModel pggSwappedDihedralGenerators :=
  pggTwoReflectionData.swapOrderTwo rfl

private def pggSwappedDihedralNormalForm :
    DihedralLatticeNormalForm pggModel pggSwappedDihedralGenerators :=
  pggDihedralNormalForm.swapOrderTwoPrimitive rfl

private theorem pggSwappedTwoReflectionData_firstShiftClass_ne_zero :
    pggSwappedTwoReflectionData.firstShiftClass ≠ 0 := by
  apply TwoReflectionExtensionData.firstShiftClass_ne_zero_of_sq_translationPart
    pggSwappedDihedralNormalForm pggSwappedTwoReflectionData
  · rfl
  · change translationPart
        (((finiteCosetLift pggCosetData (.sr 1) : pggModel.carrier) :
          EuclideanMotion Plane) ^ 2) =
        (pggSwappedDihedralNormalForm.basis 0 : Plane)
    rw [finiteCosetLift_sq_translationPart]
    change pggShift (.sr 1) +
        pmmCosetData.linearRep (.sr 1) (pggShift (.sr 1)) = _
    rw [show (pggSwappedDihedralNormalForm.basis 0 : Plane) = squareBasisOne by
      change
        ((pggDihedralNormalForm.swappedBasis 0 :
          pggModel.translationLattice.carrier) : Plane) = _
      rw [DihedralLatticeNormalForm.swappedBasis, Module.Basis.reindex_apply]
      change (pggDihedralNormalForm.basis 1 : Plane) = _
      rfl,
      pggShift_sr_one, map_smul, pmmLinear_sr_one_squareBasisOne]
    module

/-- The second canonical `pgg` family has nonzero quotient-valued glide class. -/
theorem pggTwoReflectionData_secondShiftClass_ne_zero :
    pggTwoReflectionData.secondShiftClass ≠ 0 := by
  intro hzero
  apply pggSwappedTwoReflectionData_firstShiftClass_ne_zero
  change (pggTwoReflectionData.swapOrderTwo rfl).firstShiftClass = 0
  exact (TwoReflectionExtensionData.swapOrderTwo_firstShiftClass_eq_zero_iff
    pggTwoReflectionData rfl).2 hzero

/-- The first canonical `p4g` family has nonzero quotient-valued glide class. -/
theorem p4gTwoReflectionData_firstShiftClass_ne_zero :
    p4gTwoReflectionData.firstShiftClass ≠ 0 := by
  apply TwoReflectionExtensionData.firstShiftClass_ne_zero_of_sq_translationPart
    p4gDihedralNormalForm p4gTwoReflectionData
  · rfl
  · change translationPart
        (((finiteCosetLift p4gCosetData (.sr 0) : p4gModel.carrier) :
          EuclideanMotion Plane) ^ 2) =
        (p4gDihedralNormalForm.basis 0 : Plane)
    rw [finiteCosetLift_sq_translationPart]
    change p4gGlideShift +
        p4mCosetData.linearRep (.sr 0) p4gGlideShift = _
    rw [show (p4gDihedralNormalForm.basis 0 : Plane) = squareBasisZero by rfl,
      p4mLinear_sr_zero_p4gGlideShift]
    simp only [p4gGlideShift]
    module

/-- The second canonical `p4g` family is a mirror family. -/
theorem p4gTwoReflectionData_secondShiftClass_eq_zero :
    p4gTwoReflectionData.secondShiftClass = 0 := by
  apply TwoReflectionExtensionData.secondShiftClass_eq_zero_of_sq_translationPart
  change translationPart
      (((finiteCosetLift p4gCosetData (.sr 1) : p4gModel.carrier) :
        EuclideanMotion Plane) ^ 2) = 0
  rw [finiteCosetLift_sq_translationPart]
  change p4gGlideShift +
      p4mCosetData.linearRep (.sr 1) p4gGlideShift = 0
  rw [p4mLinear_sr_one_p4gGlideShift]
  module

/-- The lattice form advertised by each multiple-reflection standard model. -/
def MultipleReflectionType.latticeForm : MultipleReflectionType → DihedralLatticeForm
  | .cmm => .orderTwoCentered
  | .pmm | .pmg | .pgg => .orderTwoPrimitive
  | .p3m1 => .p3m1
  | .p31m => .p31m
  | .p4m | .p4g => .orderFour
  | .p6m => .orderSix

/-- All concrete generator, simultaneous-normal-form, and adjacent-lift data for one of the
nine multiple-reflection standard models. -/
structure MultipleReflectionModelData (w : MultipleReflectionType) where
  d : DihedralGenerators w.model
  N : DihedralLatticeNormalForm w.model d
  c : TwoReflectionExtensionData w.model d
  form_eq : N.form = w.latticeForm

/-- The complete transparent model data used by the M6 comparison theorems. -/
def multipleReflectionModelData :
    (w : MultipleReflectionType) → MultipleReflectionModelData w
  | .cmm =>
      ⟨cmmDihedralGenerators, cmmDihedralNormalForm,
        cmmTwoReflectionData, rfl⟩
  | .pmm =>
      ⟨pmmDihedralGenerators, pmmDihedralNormalForm,
        pmmTwoReflectionData, rfl⟩
  | .pmg =>
      ⟨pmgDihedralGenerators, pmgDihedralNormalForm,
        pmgTwoReflectionData, rfl⟩
  | .pgg =>
      ⟨pggDihedralGenerators, pggDihedralNormalForm,
        pggTwoReflectionData, rfl⟩
  | .p3m1 =>
      ⟨p3m1DihedralGenerators, p3m1DihedralNormalForm,
        p3m1TwoReflectionData, rfl⟩
  | .p31m =>
      ⟨p31mDihedralGenerators, p31mDihedralNormalForm,
        p31mTwoReflectionData, rfl⟩
  | .p4m =>
      ⟨p4mDihedralGenerators, p4mDihedralNormalForm,
        p4mTwoReflectionData, rfl⟩
  | .p4g =>
      ⟨p4gDihedralGenerators, p4gDihedralNormalForm,
        p4gTwoReflectionData, rfl⟩
  | .p6m =>
      ⟨p6mDihedralGenerators, p6mDihedralNormalForm,
        p6mTwoReflectionData, rfl⟩

end


end WallpaperGroups
