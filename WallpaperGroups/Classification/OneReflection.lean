import WallpaperGroups.Classification.NoReflections
import WallpaperGroups.Invariants.ShiftClass
import WallpaperGroups.Models.ReflectionModels
import WallpaperGroups.Presentations.ReflectionExtension
import WallpaperGroups.Restriction.ReflectionNormalForms

set_option linter.style.header false

/-!
# Classification with one reflection

This file classifies the point-order-two case with a single reversing point element.  It combines
the quotient-valued shift invariant with the two integral reflection normal forms and the reusable
two-coset extension comparison.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-- The point group has one nonidentity reflection when the positive subgroup is trivial and a
reversing point element exists. -/
def PointGroupHasOneReflection (G : PlaneGroup) : Prop :=
  ∃ s : pointGroup G.carrier,
    s ∉ orientationPreservingPointGroup G ∧
      ∀ r : orientationPreservingPointGroup G, r = 1

noncomputable def oneReflectionGenerator
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G) :
    pointGroup G.carrier :=
  Classical.choose hG

theorem oneReflectionGenerator_reversing
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G) :
    oneReflectionGenerator G hG ∉ orientationPreservingPointGroup G :=
  (Classical.choose_spec hG).1

theorem oneReflectionGenerator_ne_one
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G) :
    oneReflectionGenerator G hG ≠ 1 := by
  intro h
  apply oneReflectionGenerator_reversing G hG
  rw [h]
  exact (orientationPreservingPointGroup G).one_mem

theorem oneReflectionGenerator_cases
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G)
    (q : pointGroup G.carrier) :
    q = 1 ∨ q = oneReflectionGenerator G hG := by
  let s := oneReflectionGenerator G hG
  have hs : s ∉ orientationPreservingPointGroup G :=
    oneReflectionGenerator_reversing G hG
  rcases pointGroup_rotation_or_reflection_mul G s hs q with hq | ⟨r, hr⟩
  · left
    have hrone : (⟨q, hq⟩ : orientationPreservingPointGroup G) = 1 :=
      (Classical.choose_spec hG).2 ⟨q, hq⟩
    exact congrArg Subtype.val hrone
  · right
    have hrone : r = 1 := (Classical.choose_spec hG).2 r
    simpa [s, hrone] using hr

theorem oneReflectionGenerator_sq
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G) :
    oneReflectionGenerator G hG ^ 2 = 1 :=
  pointGroup_reversing_sq G _ (oneReflectionGenerator_reversing G hG)

/-- Canonical selected-lift presentation data for a point group with one reflection. -/
noncomputable def reflectionExtensionDataOfOneReflection
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G) :
    ReflectionExtensionData G := by
  let s := oneReflectionGenerator G hG
  let g : G.carrier := Classical.choose (pointProjection_surjective G.carrier s)
  have hg : pointProjection G.carrier g = s :=
    Classical.choose_spec (pointProjection_surjective G.carrier s)
  have hs2 : s ^ 2 = 1 := oneReflectionGenerator_sq G hG
  let v : translationVectors G.carrier :=
    ⟨translationPart ((g : EuclideanMotion Plane) ^ 2),
      lift_pow_translationPart_mem G.carrier g 2 (by simpa [hg] using hs2)⟩
  refine
    { generator := s
      generator_ne_one := oneReflectionGenerator_ne_one G hG
      generator_cases := oneReflectionGenerator_cases G hG
      lift := g
      lift_projection := hg
      shift := v
      lift_sq := ?_ }
  apply Subtype.ext
  change (g : EuclideanMotion Plane) ^ 2 = translation (v : Plane)
  exact lift_pow_eq_translation G.carrier g 2 (by simpa [hg] using hs2)

/-- The three equivalence classes with a single reflection. -/
inductive OneReflectionType
  | cm
  | pm
  | pg
  deriving DecidableEq, Fintype

/-- The corresponding transparent standard model. -/
def OneReflectionType.model : OneReflectionType → PlaneGroup
  | .cm => cmModel
  | .pm => pmModel
  | .pg => pgModel

lemma eq_one_or_eq_of_mem_zpowers_of_sq_eq_one
    {P : Type*} [Group P] (r x : P) (hr : r ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers r) : x = 1 ∨ x = r := by
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [zpow_eq_zpow_emod' k hr]
  have hk0 : 0 ≤ k % ((2 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hk2 : k % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have hk : k % ((2 : ℕ) : ℤ) = 0 ∨
      k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk with hk | hk
  · left
    rw [hk]
    simp
  · right
    rw [hk]
    simp

def pmReflection : pointGroup pmModel.carrier :=
  ⟨axisReflection, by
    rw [pmModel_pointGroup]
    exact Subgroup.mem_zpowers axisReflection⟩

def cmReflection : pointGroup cmModel.carrier :=
  ⟨axisReflection, by
    rw [cmModel_pointGroup]
    exact Subgroup.mem_zpowers axisReflection⟩

def pgReflection : pointGroup pgModel.carrier :=
  ⟨axisReflection, by
    rw [pgModel_pointGroup]
    exact Subgroup.mem_zpowers axisReflection⟩

lemma axisReflection_pow_two : axisReflection ^ 2 = 1 := by
  change axisReflection * axisReflection = 1
  exact axisReflection_sq

theorem pmReflection_cases (q : pointGroup pmModel.carrier) :
    q = 1 ∨ q = pmReflection := by
  have hq : (q : Plane ≃ₗᵢ[ℝ] Plane) ∈ Subgroup.zpowers axisReflection := by
    rw [← pmModel_pointGroup]
    exact q.property
  rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one axisReflection q.1
      axisReflection_pow_two hq with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

theorem cmReflection_cases (q : pointGroup cmModel.carrier) :
    q = 1 ∨ q = cmReflection := by
  have hq : (q : Plane ≃ₗᵢ[ℝ] Plane) ∈ Subgroup.zpowers axisReflection := by
    rw [← cmModel_pointGroup]
    exact q.property
  rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one axisReflection q.1
      axisReflection_pow_two hq with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

theorem pgReflection_cases (q : pointGroup pgModel.carrier) :
    q = 1 ∨ q = pgReflection := by
  have hq : (q : Plane ≃ₗᵢ[ℝ] Plane) ∈ Subgroup.zpowers axisReflection := by
    rw [← pgModel_pointGroup]
    exact q.property
  rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one axisReflection q.1
      axisReflection_pow_two hq with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

lemma modelReflection_reversing
    (G : PlaneGroup) (r : pointGroup G.carrier)
    (hr : (r : Plane ≃ₗᵢ[ℝ] Plane) = axisReflection) :
    r ∉ orientationPreservingPointGroup G := by
  intro h
  change 0 < ((pointGroupDet G r : ℝˣ) : ℝ) at h
  rw [pointGroupDet_apply, hr, axisReflection_det] at h
  norm_num at h

theorem pmModel_hasOneReflection : PointGroupHasOneReflection pmModel := by
  refine ⟨pmReflection, modelReflection_reversing pmModel pmReflection rfl, ?_⟩
  intro r
  rcases pmReflection_cases r.1 with h | h
  · exact Subtype.ext h
  · exfalso
    have hr : (r.1 : Plane ≃ₗᵢ[ℝ] Plane) = axisReflection := by
      simpa [pmReflection] using congrArg Subtype.val h
    exact modelReflection_reversing pmModel r.1 hr r.2

theorem cmModel_hasOneReflection : PointGroupHasOneReflection cmModel := by
  refine ⟨cmReflection, modelReflection_reversing cmModel cmReflection rfl, ?_⟩
  intro r
  rcases cmReflection_cases r.1 with h | h
  · exact Subtype.ext h
  · exfalso
    have hr : (r.1 : Plane ≃ₗᵢ[ℝ] Plane) = axisReflection := by
      simpa [cmReflection] using congrArg Subtype.val h
    exact modelReflection_reversing cmModel r.1 hr r.2

theorem pgModel_hasOneReflection : PointGroupHasOneReflection pgModel := by
  refine ⟨pgReflection, modelReflection_reversing pgModel pgReflection rfl, ?_⟩
  intro r
  rcases pgReflection_cases r.1 with h | h
  · exact Subtype.ext h
  · exfalso
    have hr : (r.1 : Plane ≃ₗᵢ[ℝ] Plane) = axisReflection := by
      simpa [pgReflection] using congrArg Subtype.val h
    exact modelReflection_reversing pgModel r.1 hr r.2

def pmReflectionLift : pmModel.carrier :=
  ⟨shiftedReflectionLift axisReflection 0, by
    unfold pmModel shiftedReflectionPlaneGroup
    exact shiftedReflectionLift_mem RankTwoLattice.standardLattice axisReflection 0
      axisReflection_mem_squareStabilizer axisReflection_sq (by simp)⟩

def cmReflectionLift : cmModel.carrier :=
  ⟨shiftedReflectionLift axisReflection 0, by
    unfold cmModel shiftedReflectionPlaneGroup
    exact shiftedReflectionLift_mem centeredLattice axisReflection 0
      axisReflection_mem_centeredStabilizer axisReflection_sq (by simp)⟩

def pgReflectionLift : pgModel.carrier :=
  ⟨shiftedReflectionLift axisReflection glideShift, by
    unfold pgModel shiftedReflectionPlaneGroup
    exact shiftedReflectionLift_mem RankTwoLattice.standardLattice axisReflection glideShift
      axisReflection_mem_squareStabilizer axisReflection_sq glideShift_norm_mem⟩

@[simp] theorem pmReflectionLift_projection :
    pointProjection pmModel.carrier pmReflectionLift = pmReflection := by
  apply Subtype.ext
  exact shiftedReflectionLift_linearPart axisReflection 0

@[simp] theorem cmReflectionLift_projection :
    pointProjection cmModel.carrier cmReflectionLift = cmReflection := by
  apply Subtype.ext
  exact shiftedReflectionLift_linearPart axisReflection 0

@[simp] theorem pgReflectionLift_projection :
    pointProjection pgModel.carrier pgReflectionLift = pgReflection := by
  apply Subtype.ext
  exact shiftedReflectionLift_linearPart axisReflection glideShift

def pgReflectionShift : translationVectors pgModel.carrier :=
  pgModel.latticeTranslationEquiv (pgModel.translationLattice.basis 0)

@[simp] theorem pgReflectionShift_coe :
    (pgReflectionShift : Plane) =
      (RankTwoLattice.standardLattice.basis 0 : Plane) := by
  rfl

def pmReflectionExtensionData : ReflectionExtensionData pmModel where
  generator := pmReflection
  generator_ne_one := by
    intro h
    exact (modelReflection_reversing pmModel pmReflection rfl)
      (by rw [h]; exact (orientationPreservingPointGroup pmModel).one_mem)
  generator_cases := pmReflection_cases
  lift := pmReflectionLift
  lift_projection := pmReflectionLift_projection
  shift := 0
  lift_sq := by
    apply Subtype.ext
    change (shiftedReflectionLift axisReflection 0) ^ 2 = translation (0 : Plane)
    rw [pmModel_lift_sq, translation_zero]

def cmReflectionExtensionData : ReflectionExtensionData cmModel where
  generator := cmReflection
  generator_ne_one := by
    intro h
    exact (modelReflection_reversing cmModel cmReflection rfl)
      (by rw [h]; exact (orientationPreservingPointGroup cmModel).one_mem)
  generator_cases := cmReflection_cases
  lift := cmReflectionLift
  lift_projection := cmReflectionLift_projection
  shift := 0
  lift_sq := by
    apply Subtype.ext
    change (shiftedReflectionLift axisReflection 0) ^ 2 = translation (0 : Plane)
    rw [cmModel_lift_sq, translation_zero]

def pgReflectionExtensionData : ReflectionExtensionData pgModel where
  generator := pgReflection
  generator_ne_one := by
    intro h
    exact (modelReflection_reversing pgModel pgReflection rfl)
      (by rw [h]; exact (orientationPreservingPointGroup pgModel).one_mem)
  generator_cases := pgReflection_cases
  lift := pgReflectionLift
  lift_projection := pgReflectionLift_projection
  shift := pgReflectionShift
  lift_sq := by
    apply Subtype.ext
    change (shiftedReflectionLift axisReflection glideShift) ^ 2 =
      translation (pgReflectionShift : Plane)
    rw [pgModel_lift_sq, pgReflectionShift_coe]


def pmReflectionNormalForm :
    PlaneGroup.ReflectionLatticeNormalForm pmModel pmReflection where
  kind := .primitive
  basis := pmModel.translationLattice.basis
  matrix_eq := by
    apply IntegralReflection.toMatrix_eq_reflectionLatticeMatrix
    · apply Subtype.ext
      exact axisReflection_standard_basis_zero
    · apply Subtype.ext
      exact axisReflection_standard_basis_one

def pgReflectionNormalForm :
    PlaneGroup.ReflectionLatticeNormalForm pgModel pgReflection where
  kind := .primitive
  basis := pgModel.translationLattice.basis
  matrix_eq := by
    apply IntegralReflection.toMatrix_eq_reflectionLatticeMatrix
    · apply Subtype.ext
      exact axisReflection_standard_basis_zero
    · apply Subtype.ext
      exact axisReflection_standard_basis_one

def cmReflectionNormalForm :
    PlaneGroup.ReflectionLatticeNormalForm cmModel cmReflection where
  kind := .centered
  basis := cmModel.translationLattice.basis
  matrix_eq := by
    apply IntegralReflection.toMatrix_eq_reflectionLatticeMatrix
    · apply Subtype.ext
      exact axisReflection_centered_basis_zero
    · apply Subtype.ext
      exact axisReflection_centered_basis_one

@[simp]
theorem finiteNormHom_two (G : PlaneGroup) (s : pointGroup G.carrier)
    (t : translationVectors G.carrier) :
    finiteNormHom G s 2 t = t + pointAction G.carrier s t := by
  simp [finiteNormHom_apply, Finset.sum_range_succ]

theorem pmReflection_sq : pmReflection ^ 2 = 1 := by
  apply Subtype.ext
  exact axisReflection_pow_two

theorem pgReflection_sq : pgReflection ^ 2 = 1 := by
  apply Subtype.ext
  exact axisReflection_pow_two

def pmShiftClass : ShiftClassGroup pmModel pmReflection 2 pmReflection_sq :=
  shiftClass pmModel pmReflection 2 pmReflection_sq
    pmReflectionLift pmReflectionLift_projection

def pgShiftClass : ShiftClassGroup pgModel pgReflection 2 pgReflection_sq :=
  shiftClass pgModel pgReflection 2 pgReflection_sq
    pgReflectionLift pgReflectionLift_projection

theorem pmShiftClass_eq_zero : pmShiftClass = 0 := by
  rw [pmShiftClass, shiftClass_eq_zero_iff]
  refine ⟨0, ?_⟩
  apply Subtype.ext
  change finiteNormHom pmModel pmReflection 2 0 =
    liftPowerTranslation pmModel pmReflection 2 pmReflection_sq
      pmReflectionLift pmReflectionLift_projection
  simp only [map_zero]
  apply Subtype.ext
  change 0 = translationPart
    ((shiftedReflectionLift axisReflection 0) ^ 2)
  rw [pmModel_lift_sq, translationPart_one]

theorem pgShiftClass_ne_zero : pgShiftClass ≠ 0 := by
  intro hz
  have hmem := (shiftClass_eq_zero_iff pgModel pgReflection 2 pgReflection_sq
    pgReflectionLift pgReflectionLift_projection).mp hz
  rcases hmem with ⟨u, hu⟩
  apply pgReflectionNormalForm.primitive_basis_zero_not_mem_reflectionNormRange rfl
  rw [PlaneGroup.mem_reflectionNormRange_iff]
  let uL : pgModel.translationLattice.carrier :=
    pgModel.latticeTranslationEquiv.symm u
  refine ⟨uL, ?_⟩
  apply pgModel.latticeTranslationEquiv.injective
  change u + pointAction pgModel.carrier pgReflection u = pgReflectionShift
  have huv := congrArg Subtype.val hu
  change finiteNormHom pgModel pgReflection 2 u =
      liftPowerTranslation pgModel pgReflection 2 pgReflection_sq
        pgReflectionLift pgReflectionLift_projection at huv
  rw [finiteNormHom_two] at huv
  have hlift : liftPowerTranslation pgModel pgReflection 2 pgReflection_sq
      pgReflectionLift pgReflectionLift_projection = pgReflectionShift := by
    apply Subtype.ext
    change translationPart ((shiftedReflectionLift axisReflection glideShift) ^ 2) =
      (pgReflectionShift : Plane)
    rw [pgModel_lift_sq, translationPart_translation, pgReflectionShift_coe]
  rw [hlift] at huv
  exact huv

theorem ReflectionExtensionData.shift_eq_liftPowerTranslation
    {G : PlaneGroup} (c : ReflectionExtensionData G)
    (hsq : c.generator ^ 2 = 1) :
    c.shift = liftPowerTranslation G c.generator 2 hsq c.lift c.lift_projection := by
  apply Subtype.ext
  have h := congrArg (fun z : G.carrier => (z : EuclideanMotion Plane)) c.lift_sq
  have ht := congrArg translationPart h
  change (c.shift : Plane) = translationPart ((c.lift : EuclideanMotion Plane) ^ 2)
  simpa using ht.symm

theorem ReflectionExtensionData.shift_fixed
    {G : PlaneGroup} (c : ReflectionExtensionData G)
    (hsq : c.generator ^ 2 = 1) :
    pointAction G.carrier c.generator c.shift = c.shift := by
  rw [c.shift_eq_liftPowerTranslation hsq]
  exact (liftPowerFixedTranslation G c.generator 2 hsq c.lift c.lift_projection).property

def reflectionStoredShift {G : PlaneGroup} (c : ReflectionExtensionData G) :
    G.translationLattice.carrier :=
  G.latticeTranslationEquiv.symm c.shift

theorem reflectionStoredShift_fixed
    {G : PlaneGroup} (c : ReflectionExtensionData G)
    (hsq : c.generator ^ 2 = 1) :
    reflectionStoredShift c ∈ G.reflectionFixedSubmodule c.generator := by
  rw [PlaneGroup.mem_reflectionFixedSubmodule_iff]
  apply G.latticeTranslationEquiv.injective
  rw [TranslationPreservingIso.latticeTranslationEquiv_latticeAction]
  change pointAction G.carrier c.generator c.shift = c.shift
  exact c.shift_fixed hsq

@[simp]
theorem translationVectorEquivOfLatticeEquiv_latticeTranslation
    (G H : PlaneGroup)
    (eL : G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier)
    (t : G.translationLattice.carrier) :
    translationVectorEquivOfLatticeEquiv G H eL
        (G.latticeTranslationEquiv t) =
      H.latticeTranslationEquiv (eL t) := by
  simp [translationVectorEquivOfLatticeEquiv]

theorem reflectionNormVector_latticeTranslation
    {G : PlaneGroup} (c : ReflectionExtensionData G)
    (u : G.translationLattice.carrier) :
    reflectionNormVector c (G.latticeTranslationEquiv u) =
      G.latticeTranslationEquiv (u + G.latticeAction c.generator u) := by
  apply Subtype.ext
  rfl

set_option maxRecDepth 2000 in
theorem equivalent_cm_of_centered
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G)
    (N : G.ReflectionLatticeNormalForm (oneReflectionGenerator G hG))
    (hkind : N.kind = .centered) :
    PlaneGroup.Equivalent G cmModel := by
  let cG := reflectionExtensionDataOfOneReflection G hG
  have hgen : cG.generator = oneReflectionGenerator G hG := rfl
  let eL : G.translationLattice.carrier ≃ₗ[ℤ] cmModel.translationLattice.carrier :=
    basisLinearEquiv N.basis cmReflectionNormalForm.basis
  have hL : ∀ t : G.translationLattice.carrier,
      eL (G.latticeAction cG.generator t) =
        cmModel.latticeAction cmReflection (eL t) := by
    intro t
    have hmat :
        LinearMap.toMatrix N.basis N.basis
            (G.latticeAction cG.generator).toLinearMap =
          LinearMap.toMatrix cmReflectionNormalForm.basis
            cmReflectionNormalForm.basis
              (cmModel.latticeAction cmReflection).toLinearMap := by
      calc
        _ = IntegralReflection.reflectionLatticeMatrix N.kind := by
          simpa [hgen] using N.matrix_eq
        _ = IntegralReflection.reflectionLatticeMatrix .centered := by rw [hkind]
        _ = _ := cmReflectionNormalForm.matrix_eq.symm
    exact basisLinearEquiv_intertwine N.basis cmReflectionNormalForm.basis
      (G.latticeAction cG.generator) (cmModel.latticeAction cmReflection) hmat t
  let eT := translationVectorEquivOfLatticeEquiv G cmModel eL
  have hact : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction cmModel.carrier cmReflection (eT t) :=
    translationVectorEquivOfLatticeEquiv_intertwine G cmModel eL
      cG.generator cmReflection hL
  have hsq : cG.generator ^ 2 = 1 := by
    exact oneReflectionGenerator_sq G hG
  have hfixed : reflectionStoredShift cG ∈
      G.reflectionFixedSubmodule cG.generator :=
    reflectionStoredShift_fixed cG hsq
  obtain ⟨u, hu⟩ := N.centered_fixed_is_reflectionNorm hkind hfixed
  have hu' : u + G.latticeAction cG.generator u = reflectionStoredShift cG := by
    simpa [hgen] using hu
  let uH : translationVectors cmModel.carrier :=
    cmModel.latticeTranslationEquiv (eL u)
  have hshift : eT cG.shift =
      reflectionNormVector cmReflectionExtensionData uH +
        cmReflectionExtensionData.shift := by
    rw [show cG.shift = G.latticeTranslationEquiv (reflectionStoredShift cG) by
      exact (G.latticeTranslationEquiv.apply_symm_apply cG.shift).symm]
    rw [translationVectorEquivOfLatticeEquiv_latticeTranslation]
    rw [← hu']
    rw [map_add, hL]
    rw [cmModel.latticeTranslationEquiv.map_add]
    change cmModel.latticeTranslationEquiv (eL u) +
        cmModel.latticeTranslationEquiv
          (cmModel.latticeAction cmReflection (eL u)) =
      uH + pointAction cmModel.carrier cmReflection uH + 0
    rw [add_zero]
    rfl
  exact ⟨reflectionExtensionIsoOfShiftDifference G cmModel cG
    cmReflectionExtensionData eT hact uH hshift⟩

set_option maxRecDepth 2000 in
theorem equivalent_pm_of_primitive_norm
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G)
    (N : G.ReflectionLatticeNormalForm (oneReflectionGenerator G hG))
    (hkind : N.kind = .primitive)
    (hnorm : reflectionStoredShift (reflectionExtensionDataOfOneReflection G hG) ∈
      G.reflectionNormRange (oneReflectionGenerator G hG)) :
    PlaneGroup.Equivalent G pmModel := by
  let cG := reflectionExtensionDataOfOneReflection G hG
  have hgen : cG.generator = oneReflectionGenerator G hG := rfl
  let eL : G.translationLattice.carrier ≃ₗ[ℤ] pmModel.translationLattice.carrier :=
    basisLinearEquiv N.basis pmReflectionNormalForm.basis
  have hL : ∀ t : G.translationLattice.carrier,
      eL (G.latticeAction cG.generator t) =
        pmModel.latticeAction pmReflection (eL t) := by
    intro t
    have hmat :
        LinearMap.toMatrix N.basis N.basis
            (G.latticeAction cG.generator).toLinearMap =
          LinearMap.toMatrix pmReflectionNormalForm.basis
            pmReflectionNormalForm.basis
              (pmModel.latticeAction pmReflection).toLinearMap := by
      calc
        _ = IntegralReflection.reflectionLatticeMatrix N.kind := by
          simpa [hgen] using N.matrix_eq
        _ = IntegralReflection.reflectionLatticeMatrix .primitive := by rw [hkind]
        _ = _ := pmReflectionNormalForm.matrix_eq.symm
    exact basisLinearEquiv_intertwine N.basis pmReflectionNormalForm.basis
      (G.latticeAction cG.generator) (pmModel.latticeAction pmReflection) hmat t
  let eT := translationVectorEquivOfLatticeEquiv G pmModel eL
  have hact : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction pmModel.carrier pmReflection (eT t) :=
    translationVectorEquivOfLatticeEquiv_intertwine G pmModel eL
      cG.generator pmReflection hL
  rw [PlaneGroup.mem_reflectionNormRange_iff] at hnorm
  obtain ⟨u, hu⟩ := hnorm
  have hu' : u + G.latticeAction cG.generator u = reflectionStoredShift cG := by
    simpa [hgen] using hu
  let uH : translationVectors pmModel.carrier :=
    pmModel.latticeTranslationEquiv (eL u)
  have hshift : eT cG.shift =
      reflectionNormVector pmReflectionExtensionData uH +
        pmReflectionExtensionData.shift := by
    rw [show cG.shift = G.latticeTranslationEquiv (reflectionStoredShift cG) by
      exact (G.latticeTranslationEquiv.apply_symm_apply cG.shift).symm]
    rw [translationVectorEquivOfLatticeEquiv_latticeTranslation]
    rw [← hu', map_add, hL, pmModel.latticeTranslationEquiv.map_add]
    change pmModel.latticeTranslationEquiv (eL u) +
        pmModel.latticeTranslationEquiv
          (pmModel.latticeAction pmReflection (eL u)) =
      uH + pointAction pmModel.carrier pmReflection uH + 0
    rw [add_zero]
    rfl
  exact ⟨reflectionExtensionIsoOfShiftDifference G pmModel cG
    pmReflectionExtensionData eT hact uH hshift⟩

set_option maxRecDepth 2000 in
theorem equivalent_pg_of_primitive_nonNorm
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G)
    (N : G.ReflectionLatticeNormalForm (oneReflectionGenerator G hG))
    (hkind : N.kind = .primitive)
    (hnot : reflectionStoredShift (reflectionExtensionDataOfOneReflection G hG) ∉
      G.reflectionNormRange (oneReflectionGenerator G hG)) :
    PlaneGroup.Equivalent G pgModel := by
  let cG := reflectionExtensionDataOfOneReflection G hG
  have hgen : cG.generator = oneReflectionGenerator G hG := rfl
  let eL : G.translationLattice.carrier ≃ₗ[ℤ] pgModel.translationLattice.carrier :=
    basisLinearEquiv N.basis pgReflectionNormalForm.basis
  have hL : ∀ t : G.translationLattice.carrier,
      eL (G.latticeAction cG.generator t) =
        pgModel.latticeAction pgReflection (eL t) := by
    intro t
    have hmat :
        LinearMap.toMatrix N.basis N.basis
            (G.latticeAction cG.generator).toLinearMap =
          LinearMap.toMatrix pgReflectionNormalForm.basis
            pgReflectionNormalForm.basis
              (pgModel.latticeAction pgReflection).toLinearMap := by
      calc
        _ = IntegralReflection.reflectionLatticeMatrix N.kind := by
          simpa [hgen] using N.matrix_eq
        _ = IntegralReflection.reflectionLatticeMatrix .primitive := by rw [hkind]
        _ = _ := pgReflectionNormalForm.matrix_eq.symm
    exact basisLinearEquiv_intertwine N.basis pgReflectionNormalForm.basis
      (G.latticeAction cG.generator) (pgModel.latticeAction pgReflection) hmat t
  let eT := translationVectorEquivOfLatticeEquiv G pgModel eL
  have hact : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction pgModel.carrier pgReflection (eT t) :=
    translationVectorEquivOfLatticeEquiv_intertwine G pgModel eL
      cG.generator pgReflection hL
  have hsq : cG.generator ^ 2 = 1 := oneReflectionGenerator_sq G hG
  have hfixed : reflectionStoredShift cG ∈
      G.reflectionFixedSubmodule cG.generator :=
    reflectionStoredShift_fixed cG hsq
  have hdiff := N.primitive_nonzero_class_eq_basis_zero_class hkind hfixed hnot
  rw [PlaneGroup.mem_reflectionNormRange_iff] at hdiff
  obtain ⟨u, hu⟩ := hdiff
  have hu' : u + G.latticeAction cG.generator u =
      reflectionStoredShift cG - N.basis 0 := by
    simpa [hgen] using hu
  have hdecomp : reflectionStoredShift cG =
      (u + G.latticeAction cG.generator u) + N.basis 0 := by
    rw [hu']
    abel
  let uH : translationVectors pgModel.carrier :=
    pgModel.latticeTranslationEquiv (eL u)
  have hshift : eT cG.shift =
      reflectionNormVector pgReflectionExtensionData uH +
        pgReflectionExtensionData.shift := by
    rw [show cG.shift = G.latticeTranslationEquiv (reflectionStoredShift cG) by
      exact (G.latticeTranslationEquiv.apply_symm_apply cG.shift).symm]
    rw [translationVectorEquivOfLatticeEquiv_latticeTranslation]
    rw [hdecomp, eL.map_add, eL.map_add, hL]
    rw [basisLinearEquiv_apply_basis]
    rw [pgModel.latticeTranslationEquiv.map_add,
      pgModel.latticeTranslationEquiv.map_add]
    change pgModel.latticeTranslationEquiv (eL u) +
          pgModel.latticeTranslationEquiv
            (pgModel.latticeAction pgReflection (eL u)) +
        pgModel.latticeTranslationEquiv (pgReflectionNormalForm.basis 0) =
      uH + pointAction pgModel.carrier pgReflection uH + pgReflectionShift
    rfl
  exact ⟨reflectionExtensionIsoOfShiftDifference G pgModel cG
    pgReflectionExtensionData eT hact uH hshift⟩

/-- Centered and primitive reflection actions cannot be related by a
translation-preserving isomorphism. -/
theorem not_translationPreservingIso_centered_primitive
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (sG : pointGroup G.carrier) (sH : pointGroup H.carrier)
    (hgen : e.pointGroupEquiv sG = sH)
    (NG : G.ReflectionLatticeNormalForm sG)
    (NH : H.ReflectionLatticeNormalForm sH)
    (hcentered : NG.kind = .centered) (hprimitive : NH.kind = .primitive) :
    False := by
  let tH : H.translationLattice.carrier := NH.basis 0
  let tG : G.translationLattice.carrier := e.translationLatticeEquiv.symm tH
  have htHfixed : tH ∈ H.reflectionFixedSubmodule sH :=
    NH.primitive_basis_zero_mem_fixed hprimitive
  have htGfixed : tG ∈ G.reflectionFixedSubmodule sG := by
    rw [PlaneGroup.mem_reflectionFixedSubmodule_iff]
    apply e.translationLatticeEquiv.injective
    rw [e.translationLattice_pointAction]
    rw [e.translationLatticeEquiv.apply_symm_apply]
    rw [hgen]
    exact (PlaneGroup.mem_reflectionFixedSubmodule_iff H sH tH).mp htHfixed
  obtain ⟨uG, huG⟩ := NG.centered_fixed_is_reflectionNorm hcentered htGfixed
  apply NH.primitive_basis_zero_not_mem_reflectionNormRange hprimitive
  rw [PlaneGroup.mem_reflectionNormRange_iff]
  refine ⟨e.translationLatticeEquiv uG, ?_⟩
  calc
    e.translationLatticeEquiv uG +
          H.latticeAction sH (e.translationLatticeEquiv uG) =
        e.translationLatticeEquiv uG +
          H.latticeAction (e.pointGroupEquiv sG)
            (e.translationLatticeEquiv uG) := by rw [hgen]
    _ = e.translationLatticeEquiv
          (uG + G.latticeAction sG uG) := by
      rw [← e.translationLattice_pointAction, e.translationLatticeEquiv.map_add]
    _ = e.translationLatticeEquiv tG := by rw [huG]
    _ = tH := e.translationLatticeEquiv.apply_symm_apply tH

theorem pointGroupEquiv_maps_modelReflection
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (rG : pointGroup G.carrier) (rH : pointGroup H.carrier)
    (hrG : rG ≠ 1) (hcases : ∀ q : pointGroup H.carrier, q = 1 ∨ q = rH) :
    e.pointGroupEquiv rG = rH := by
  rcases hcases (e.pointGroupEquiv rG) with h | h
  · exfalso
    apply hrG
    apply e.pointGroupEquiv.injective
    simpa using h
  · exact h

theorem cmReflection_ne_one : cmReflection ≠ 1 := by
  intro h
  apply modelReflection_reversing cmModel cmReflection rfl
  rw [h]
  exact (orientationPreservingPointGroup cmModel).one_mem

theorem pmReflection_ne_one : pmReflection ≠ 1 := by
  intro h
  apply modelReflection_reversing pmModel pmReflection rfl
  rw [h]
  exact (orientationPreservingPointGroup pmModel).one_mem

theorem pgReflection_ne_one : pgReflection ≠ 1 := by
  intro h
  apply modelReflection_reversing pgModel pgReflection rfl
  rw [h]
  exact (orientationPreservingPointGroup pgModel).one_mem

theorem not_equivalent_cm_pm : ¬ PlaneGroup.Equivalent cmModel pmModel := by
  rintro ⟨e⟩
  exact not_translationPreservingIso_centered_primitive e cmReflection pmReflection
    (pointGroupEquiv_maps_modelReflection e cmReflection pmReflection
      cmReflection_ne_one pmReflection_cases)
    cmReflectionNormalForm pmReflectionNormalForm rfl rfl

theorem not_equivalent_cm_pg : ¬ PlaneGroup.Equivalent cmModel pgModel := by
  rintro ⟨e⟩
  exact not_translationPreservingIso_centered_primitive e cmReflection pgReflection
    (pointGroupEquiv_maps_modelReflection e cmReflection pgReflection
      cmReflection_ne_one pgReflection_cases)
    cmReflectionNormalForm pgReflectionNormalForm rfl rfl

/-- Vanishing does not depend on how a propositionally equal point element and
its finite-order/lift proofs are presented. -/
theorem shiftClass_eq_zero_congr_point
    {G : PlaneGroup} {h k : pointGroup G.carrier} (hhk : h = k)
    (q : ℕ) (hq : h ^ q = 1) (kq : k ^ q = 1)
    (g : G.carrier) (hg : pointProjection G.carrier g = h)
    (kg : pointProjection G.carrier g = k) :
    shiftClass G h q hq g hg = 0 ↔ shiftClass G k q kq g kg = 0 := by
  subst k
  rfl

theorem not_equivalent_pm_pg : ¬ PlaneGroup.Equivalent pmModel pgModel := by
  rintro ⟨e⟩
  have hmap : e.pointGroupEquiv pmReflection = pgReflection :=
    pointGroupEquiv_maps_modelReflection e pmReflection pgReflection
      pmReflection_ne_one pgReflection_cases
  have hmapped :=
    (shiftClass_eq_zero_iff_map e pmReflection 2 pmReflection_sq
      pmReflectionLift pmReflectionLift_projection).mp pmShiftClass_eq_zero
  have hproj : pointProjection pgModel.carrier (e.toMulEquiv pmReflectionLift) =
      pgReflection := (mappedLiftProjection e pmReflection pmReflectionLift
        pmReflectionLift_projection).trans hmap
  have hmapped' :
      shiftClass pgModel pgReflection 2 pgReflection_sq
        (e.toMulEquiv pmReflectionLift) hproj = 0 := by
    exact (shiftClass_eq_zero_congr_point hmap 2
      (transportedPointPowerProof e pmReflection 2 pmReflection_sq)
      pgReflection_sq (e.toMulEquiv pmReflectionLift)
      (mappedLiftProjection e pmReflection pmReflectionLift
        pmReflectionLift_projection) hproj).mp hmapped
  have hind := shiftClass_lift_independent pgModel pgReflection 2 pgReflection_sq
    (e.toMulEquiv pmReflectionLift) pgReflectionLift hproj pgReflectionLift_projection
  apply pgShiftClass_ne_zero
  unfold pgShiftClass
  exact hind.symm.trans hmapped'

/-- Every one-reflection plane group is equivalent to one of the three models. -/
theorem exists_equivalent_oneReflectionModel
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G) :
    ∃ w : OneReflectionType, PlaneGroup.Equivalent G w.model := by
  obtain ⟨N⟩ := G.exists_reflectionLatticeNormalForm
    (oneReflectionGenerator G hG) (oneReflectionGenerator_reversing G hG)
  cases hkind : N.kind with
  | primitive =>
      by_cases hnorm :
          reflectionStoredShift (reflectionExtensionDataOfOneReflection G hG) ∈
            G.reflectionNormRange (oneReflectionGenerator G hG)
      · exact ⟨.pm, equivalent_pm_of_primitive_norm G hG N hkind hnorm⟩
      · exact ⟨.pg, equivalent_pg_of_primitive_nonNorm G hG N hkind hnorm⟩
  | centered =>
      exact ⟨.cm, equivalent_cm_of_centered G hG N hkind⟩

/-- Every standard one-reflection model has exactly one reflection. -/
theorem oneReflectionModel_hasOneReflection (w : OneReflectionType) :
    PointGroupHasOneReflection w.model := by
  cases w with
  | cm => exact cmModel_hasOneReflection
  | pm => exact pmModel_hasOneReflection
  | pg => exact pgModel_hasOneReflection

/-- The three standard one-reflection models are pairwise inequivalent. -/
theorem oneReflectionModels_equivalent_iff (w v : OneReflectionType) :
    PlaneGroup.Equivalent w.model v.model ↔ w = v := by
  constructor
  · intro h
    cases w <;> cases v
    · rfl
    · exact (not_equivalent_cm_pm h).elim
    · exact (not_equivalent_cm_pg h).elim
    · exact (not_equivalent_cm_pm (PlaneGroup.Equivalent.symm h)).elim
    · rfl
    · exact (not_equivalent_pm_pg h).elim
    · exact (not_equivalent_cm_pg (PlaneGroup.Equivalent.symm h)).elim
    · exact (not_equivalent_pm_pg (PlaneGroup.Equivalent.symm h)).elim
    · rfl
  · rintro rfl
    exact PlaneGroup.Equivalent.refl _

/-- Exactly one of `cm`, `pm`, and `pg` represents a one-reflection plane group. -/
theorem classify_one_reflection
    (G : PlaneGroup) (hG : PointGroupHasOneReflection G) :
    ∃! w : OneReflectionType, PlaneGroup.Equivalent G w.model := by
  obtain ⟨w, hw⟩ := exists_equivalent_oneReflectionModel G hG
  refine ⟨w, hw, ?_⟩
  intro v hv
  apply (oneReflectionModels_equivalent_iff v w).mp
  exact PlaneGroup.Equivalent.trans (PlaneGroup.Equivalent.symm hv) hw

end

end WallpaperGroups
