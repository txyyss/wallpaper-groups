import WallpaperGroups.Classification.NoReflections
import WallpaperGroups.Models.DihedralModels
import WallpaperGroups.Presentations.TwoReflectionExtension

set_option linter.style.header false

/-!
# Abstract comparison for plane groups with several reflections

This file is the model-independent comparison layer for the multiple-reflection classification.
Two joint dihedral lattice normal forms with the same `DihedralLatticeForm` have identical
rotation and adjacent-reflection matrices in their chosen bases.  Coordinate preservation
therefore gives an equivariant lattice equivalence, hence an equivariant equivalence of actual
translation vectors.  Once the two adjacent quotient-valued reflection shifts agree under this
equivalence, `twoReflectionExtensionIsoOfShiftClasses` identifies the full plane groups.

The nine concrete signatures and standard models are deliberately kept out of this file.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace WallpaperGroups

open EuclideanMotion
open PlaneGroup
open TwoReflectionExtensionData

noncomputable section

variable {G H : PlaneGroup}
variable {dG : DihedralGenerators G} {dH : DihedralGenerators H}

/-- The integer-linear lattice equivalence preserving coordinates in two joint normal-form
bases. -/
def sameFormLatticeEquiv
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH) :
    G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier :=
  basisLinearEquiv NG.basis NH.basis

/-- The corresponding equivalence of the actual translation-vector subgroups. -/
def sameFormTranslationEquiv
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH) :
    translationVectors G.carrier ≃+ translationVectors H.carrier :=
  translationVectorEquivOfLatticeEquiv G H (sameFormLatticeEquiv NG NH)

/-- Equal joint forms have equal selected rotation orders. -/
theorem order_eq_of_form_eq
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form) :
    dG.order = dH.order := by
  calc
    dG.order = NG.form.order := NG.order_eq.symm
    _ = NH.form.order := congrArg DihedralLatticeForm.order hform
    _ = dH.order := NH.order_eq

/-- Equal joint forms in particular give equal natural rotation orders. -/
theorem order_toNat_eq_of_form_eq
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form) :
    dG.order.toNat = dH.order.toNat :=
  congrArg DihedralRotationOrder.toNat (order_eq_of_form_eq NG NH hform)

/-- The coordinate-preserving lattice equivalence intertwines the selected rotations. -/
theorem sameFormLatticeEquiv_rotation
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (t : G.translationLattice.carrier) :
    sameFormLatticeEquiv NG NH (G.latticeAction dG.rotation.1 t) =
      H.latticeAction dH.rotation.1 (sameFormLatticeEquiv NG NH t) := by
  apply basisLinearEquiv_intertwine NG.basis NH.basis
  calc
    LinearMap.toMatrix NG.basis NG.basis
        (G.latticeAction dG.rotation.1).toLinearMap = NG.form.rotationMatrix :=
      NG.rotation_matrix_eq
    _ = NH.form.rotationMatrix := congrArg DihedralLatticeForm.rotationMatrix hform
    _ = LinearMap.toMatrix NH.basis NH.basis
        (H.latticeAction dH.rotation.1).toLinearMap := NH.rotation_matrix_eq.symm

/-- The coordinate-preserving lattice equivalence intertwines the first adjacent reflections. -/
theorem sameFormLatticeEquiv_firstReflection
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (t : G.translationLattice.carrier) :
    sameFormLatticeEquiv NG NH (G.latticeAction dG.reflection t) =
      H.latticeAction dH.reflection (sameFormLatticeEquiv NG NH t) := by
  apply basisLinearEquiv_intertwine NG.basis NH.basis
  calc
    LinearMap.toMatrix NG.basis NG.basis
        (G.latticeAction dG.reflection).toLinearMap = NG.form.reflectionMatrix :=
      NG.reflection_matrix_eq
    _ = NH.form.reflectionMatrix :=
      congrArg DihedralLatticeForm.reflectionMatrix hform
    _ = LinearMap.toMatrix NH.basis NH.basis
        (H.latticeAction dH.reflection).toLinearMap := NH.reflection_matrix_eq.symm

/-- The same equivalence also intertwines the adjacent second reflections. -/
theorem sameFormLatticeEquiv_secondReflection
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (t : G.translationLattice.carrier) :
    sameFormLatticeEquiv NG NH (G.latticeAction dG.secondReflection t) =
      H.latticeAction dH.secondReflection (sameFormLatticeEquiv NG NH t) := by
  apply basisLinearEquiv_intertwine NG.basis NH.basis
  calc
    LinearMap.toMatrix NG.basis NG.basis
        (G.latticeAction dG.secondReflection).toLinearMap =
      NG.form.secondReflectionMatrix := NG.secondReflection_matrix_eq
    _ = NH.form.secondReflectionMatrix :=
      congrArg DihedralLatticeForm.secondReflectionMatrix hform
    _ = LinearMap.toMatrix NH.basis NH.basis
        (H.latticeAction dH.secondReflection).toLinearMap :=
      NH.secondReflection_matrix_eq.symm

/-- Translation-vector form of rotation equivariance. -/
theorem sameFormTranslationEquiv_rotation
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (t : translationVectors G.carrier) :
    sameFormTranslationEquiv NG NH
        (pointAction G.carrier dG.rotation.1 t) =
      pointAction H.carrier dH.rotation.1 (sameFormTranslationEquiv NG NH t) :=
  translationVectorEquivOfLatticeEquiv_intertwine G H
    (sameFormLatticeEquiv NG NH) dG.rotation.1 dH.rotation.1
    (sameFormLatticeEquiv_rotation NG NH hform) t

/-- Translation-vector form of first-reflection equivariance. -/
theorem sameFormTranslationEquiv_firstReflection
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (t : translationVectors G.carrier) :
    sameFormTranslationEquiv NG NH
        (pointAction G.carrier dG.reflection t) =
      pointAction H.carrier dH.reflection (sameFormTranslationEquiv NG NH t) :=
  translationVectorEquivOfLatticeEquiv_intertwine G H
    (sameFormLatticeEquiv NG NH) dG.reflection dH.reflection
    (sameFormLatticeEquiv_firstReflection NG NH hform) t

/-- Translation-vector form of second-reflection equivariance. -/
theorem sameFormTranslationEquiv_secondReflection
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (t : translationVectors G.carrier) :
    sameFormTranslationEquiv NG NH
        (pointAction G.carrier dG.secondReflection t) =
      pointAction H.carrier dH.secondReflection
        (sameFormTranslationEquiv NG NH t) :=
  translationVectorEquivOfLatticeEquiv_intertwine G H
    (sameFormLatticeEquiv NG NH) dG.secondReflection dH.secondReflection
    (sameFormLatticeEquiv_secondReflection NG NH hform) t

/-! ## Comparing transported adjacent-reflection shifts -/

/-- For the first selected reflection, matching vanishing of the source and target shift classes
upgrades to equality after transport through the same-form basis equivalence. -/
theorem sameForm_firstReflection_shiftClass_eq_of_eq_zero_iff
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (x : ShiftClassGroup G dG.reflection 2 dG.reflection_sq)
    (y : ShiftClassGroup H dH.reflection 2 dH.reflection_sq)
    (hzero : x = 0 ↔ y = 0) :
    shiftClassEquivOfIntertwining (sameFormTranslationEquiv NG NH)
        dG.reflection dH.reflection
        (sameFormTranslationEquiv_firstReflection NG NH hform)
        2 dG.reflection_sq dH.reflection_sq x = y := by
  let eS := shiftClassEquivOfIntertwining (sameFormTranslationEquiv NG NH)
    dG.reflection dH.reflection
    (sameFormTranslationEquiv_firstReflection NG NH hform)
    2 dG.reflection_sq dH.reflection_sq
  have hmapzero : eS x = 0 ↔ y = 0 := by
    constructor
    · intro hx
      apply hzero.mp
      apply eS.injective
      simpa using hx
    · intro hy
      have hx : x = 0 := hzero.mpr hy
      simp [hx]
  obtain ⟨R, hR⟩ := NH.exists_firstReflectionNormalForm
  cases hkind : NH.form.firstReflectionKind with
  | primitive =>
      apply primitive_reflectionShiftClass_eq_of_eq_zero_iff
        dH.reflection_sq R (hR.trans hkind) (eS x) y hmapzero
  | centered =>
      exact
        (centered_reflectionShiftClass_eq_zero dH.reflection_sq R
          (hR.trans hkind) (eS x)).trans
        (centered_reflectionShiftClass_eq_zero dH.reflection_sq R
          (hR.trans hkind) y).symm

/-- The analogous vanishing-completeness comparison for the adjacent second reflection. -/
theorem sameForm_secondReflection_shiftClass_eq_of_eq_zero_iff
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (x : ShiftClassGroup G dG.secondReflection 2 dG.secondReflection_sq)
    (y : ShiftClassGroup H dH.secondReflection 2 dH.secondReflection_sq)
    (hzero : x = 0 ↔ y = 0) :
    shiftClassEquivOfIntertwining (sameFormTranslationEquiv NG NH)
        dG.secondReflection dH.secondReflection
        (sameFormTranslationEquiv_secondReflection NG NH hform)
        2 dG.secondReflection_sq dH.secondReflection_sq x = y := by
  let eS := shiftClassEquivOfIntertwining (sameFormTranslationEquiv NG NH)
    dG.secondReflection dH.secondReflection
    (sameFormTranslationEquiv_secondReflection NG NH hform)
    2 dG.secondReflection_sq dH.secondReflection_sq
  have hmapzero : eS x = 0 ↔ y = 0 := by
    constructor
    · intro hx
      apply hzero.mp
      apply eS.injective
      simpa using hx
    · intro hy
      have hx : x = 0 := hzero.mpr hy
      simp [hx]
  obtain ⟨R, hR⟩ := NH.exists_secondReflectionNormalForm
  cases hkind : NH.form.secondReflectionKind with
  | primitive =>
      apply primitive_reflectionShiftClass_eq_of_eq_zero_iff
        dH.secondReflection_sq R (hR.trans hkind) (eS x) y hmapzero
  | centered =>
      exact
        (centered_reflectionShiftClass_eq_zero dH.secondReflection_sq R
          (hR.trans hkind) (eS x)).trans
        (centered_reflectionShiftClass_eq_zero dH.secondReflection_sq R
          (hR.trans hkind) y).symm

/-- Same joint lattice form and the same two transported quotient shift classes determine a
translation-preserving isomorphism of the full plane groups. -/
noncomputable def twoReflectionExtensionIsoOfSameForm
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (cG : TwoReflectionExtensionData G dG)
    (cH : TwoReflectionExtensionData H dH)
    (hfirstClass :
      shiftClassEquivOfIntertwining (sameFormTranslationEquiv NG NH)
          dG.reflection dH.reflection
          (sameFormTranslationEquiv_firstReflection NG NH hform)
          2 dG.reflection_sq dH.reflection_sq cG.firstShiftClass =
        cH.firstShiftClass)
    (hsecondClass :
      shiftClassEquivOfIntertwining (sameFormTranslationEquiv NG NH)
          dG.secondReflection dH.secondReflection
          (sameFormTranslationEquiv_secondReflection NG NH hform)
          2 dG.secondReflection_sq dH.secondReflection_sq cG.secondShiftClass =
        cH.secondShiftClass) :
    TranslationPreservingIso G H := by
  apply twoReflectionExtensionIsoOfShiftClasses G H dG dH cG cH
    (sameFormTranslationEquiv NG NH)
    (order_toNat_eq_of_form_eq NG NH hform)
    (sameFormTranslationEquiv_rotation NG NH hform)
    (sameFormTranslationEquiv_firstReflection NG NH hform)
  · exact hfirstClass
  · simpa only [] using hsecondClass

/-! ## Comparing an abstract group with a standard model -/

/-- A centered first-reflection lattice action has no nontrivial quotient-valued shift class. -/
theorem firstShiftClass_eq_zero_of_centered
    (N : DihedralLatticeNormalForm G dG)
    (c : TwoReflectionExtensionData G dG)
    (hkind : N.form.firstReflectionKind = .centered) :
    c.firstShiftClass = 0 := by
  obtain ⟨R, hR⟩ := N.exists_firstReflectionNormalForm
  exact centered_reflectionShiftClass_eq_zero dG.reflection_sq R
    (hR.trans hkind) c.firstShiftClass

/-- A centered adjacent-reflection lattice action has no nontrivial quotient-valued shift
class. -/
theorem secondShiftClass_eq_zero_of_centered
    (N : DihedralLatticeNormalForm G dG)
    (c : TwoReflectionExtensionData G dG)
    (hkind : N.form.secondReflectionKind = .centered) :
    c.secondShiftClass = 0 := by
  obtain ⟨R, hR⟩ := N.exists_secondReflectionNormalForm
  exact centered_reflectionShiftClass_eq_zero dG.secondReflection_sq R
    (hR.trans hkind) c.secondShiftClass

/-- The same joint lattice form and the same vanishing pattern of the two adjacent reflection
shift classes determine the full multiple-reflection extension.  This is the reusable
same-normalized-signature equivalence theorem. -/
noncomputable def twoReflectionExtensionIsoOfSameFormAndShiftVanishing
    (NG : DihedralLatticeNormalForm G dG)
    (NH : DihedralLatticeNormalForm H dH)
    (hform : NG.form = NH.form)
    (cG : TwoReflectionExtensionData G dG)
    (cH : TwoReflectionExtensionData H dH)
    (hfirstZero : cG.firstShiftClass = 0 ↔ cH.firstShiftClass = 0)
    (hsecondZero : cG.secondShiftClass = 0 ↔ cH.secondShiftClass = 0) :
    TranslationPreservingIso G H :=
  twoReflectionExtensionIsoOfSameForm NG NH hform cG cH
    (sameForm_firstReflection_shiftClass_eq_of_eq_zero_iff
      NG NH hform cG.firstShiftClass cH.firstShiftClass hfirstZero)
    (sameForm_secondReflection_shiftClass_eq_of_eq_zero_iff
      NG NH hform cG.secondShiftClass cH.secondShiftClass hsecondZero)

/-- Matching a standard model's joint lattice form and the vanishing status of both adjacent
reflection shift classes gives a translation-preserving isomorphism to that model. -/
noncomputable def multipleReflectionModelIsoOfSameFormAndShiftVanishing
    (N : DihedralLatticeNormalForm G dG)
    (c : TwoReflectionExtensionData G dG)
    (w : MultipleReflectionType)
    (hform : N.form = w.latticeForm)
    (hfirstZero : c.firstShiftClass = 0 ↔
      (multipleReflectionModelData w).c.firstShiftClass = 0)
    (hsecondZero : c.secondShiftClass = 0 ↔
      (multipleReflectionModelData w).c.secondShiftClass = 0) :
    TranslationPreservingIso G w.model := by
  let M := multipleReflectionModelData w
  have hforms : N.form = M.N.form := hform.trans M.form_eq.symm
  exact twoReflectionExtensionIsoOfSameFormAndShiftVanishing
    N M.N hforms c M.c hfirstZero hsecondZero

/-- The standard-model first shift vanishes whenever its advertised first-reflection action is
centered. -/
private theorem model_firstShiftClass_eq_zero_of_centered
    (w : MultipleReflectionType)
    (hkind : w.latticeForm.firstReflectionKind = .centered) :
    (multipleReflectionModelData w).c.firstShiftClass = 0 := by
  let M := multipleReflectionModelData w
  apply firstShiftClass_eq_zero_of_centered M.N M.c
  exact (congrArg DihedralLatticeForm.firstReflectionKind M.form_eq).trans hkind

/-- The analogous centered-action fact for the standard model's adjacent reflection. -/
private theorem model_secondShiftClass_eq_zero_of_centered
    (w : MultipleReflectionType)
    (hkind : w.latticeForm.secondReflectionKind = .centered) :
    (multipleReflectionModelData w).c.secondShiftClass = 0 := by
  let M := multipleReflectionModelData w
  apply secondShiftClass_eq_zero_of_centered M.N M.c
  exact (congrArg DihedralLatticeForm.secondReflectionKind M.form_eq).trans hkind

private theorem eq_zero_iff_of_eq_zero
    {A B : Type*} [Zero A] [Zero B] {x : A} {y : B}
    (hx : x = 0) (hy : y = 0) : x = 0 ↔ y = 0 := by
  simp [hx, hy]

private theorem eq_zero_iff_of_ne_zero
    {A B : Type*} [Zero A] [Zero B] {x : A} {y : B}
    (hx : x ≠ 0) (hy : y ≠ 0) : x = 0 ↔ y = 0 := by
  exact ⟨(fun h => (hx h).elim), (fun h => (hy h).elim)⟩

/-- The primitive standard-model shift facts needed by the finite case split.  Centered cases
are derived uniformly from their lattice forms and do not need fields here. -/
private structure ModelShiftTable where
  pmm_first_zero : (multipleReflectionModelData .pmm).c.firstShiftClass = 0
  pmm_second_zero : (multipleReflectionModelData .pmm).c.secondShiftClass = 0
  pmg_first_zero : (multipleReflectionModelData .pmg).c.firstShiftClass = 0
  pmg_second_ne_zero : (multipleReflectionModelData .pmg).c.secondShiftClass ≠ 0
  pgg_first_ne_zero : (multipleReflectionModelData .pgg).c.firstShiftClass ≠ 0
  pgg_second_ne_zero : (multipleReflectionModelData .pgg).c.secondShiftClass ≠ 0
  p4m_first_zero : (multipleReflectionModelData .p4m).c.firstShiftClass = 0
  p4g_first_ne_zero : (multipleReflectionModelData .p4g).c.firstShiftClass ≠ 0

/-- Assuming the explicit primitive model computations, every multiple-reflection plane group
is equivalent to one of the nine standard models. -/
private theorem exists_equivalent_multipleReflectionModel_of_shiftTable
    (T : ModelShiftTable) (G : PlaneGroup)
    (hG : PointGroupHasMultipleReflections G) :
    ∃ w : MultipleReflectionType, PlaneGroup.Equivalent G w.model := by
  obtain ⟨d, ⟨N⟩⟩ := G.exists_dihedralLatticeNormalForm hG
  let c := TwoReflectionExtensionData.choose G d
  cases hform : N.form with
  | orderTwoPrimitive =>
      by_cases hfirst : c.firstShiftClass = 0
      · by_cases hsecond : c.secondShiftClass = 0
        · refine ⟨.pmm, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
            N c .pmm ?_ ?_ ?_⟩⟩
          · simpa [MultipleReflectionType.latticeForm] using hform
          · exact eq_zero_iff_of_eq_zero hfirst T.pmm_first_zero
          · exact eq_zero_iff_of_eq_zero hsecond T.pmm_second_zero
        · refine ⟨.pmg, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
            N c .pmg ?_ ?_ ?_⟩⟩
          · simpa [MultipleReflectionType.latticeForm] using hform
          · exact eq_zero_iff_of_eq_zero hfirst T.pmg_first_zero
          · exact eq_zero_iff_of_ne_zero hsecond T.pmg_second_ne_zero
      · by_cases hsecond : c.secondShiftClass = 0
        · have horder : d.order = .two := by
            rw [← N.order_eq, hform]
            rfl
          let N' := N.swapOrderTwoPrimitive hform
          let c' := c.swapOrderTwo horder
          have hfirst' : c'.firstShiftClass = 0 :=
            (c.swapOrderTwo_firstShiftClass_eq_zero_iff horder).2 hsecond
          have hsecond' : c'.secondShiftClass ≠ 0 := by
            intro hz
            exact hfirst ((c.swapOrderTwo_secondShiftClass_eq_zero_iff horder).1 hz)
          refine ⟨.pmg, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
              N' c' .pmg ?_ ?_ ?_⟩⟩
          · change (N.swapOrderTwoPrimitive hform).form =
              MultipleReflectionType.pmg.latticeForm
            simp [MultipleReflectionType.latticeForm]
          · exact eq_zero_iff_of_eq_zero hfirst' T.pmg_first_zero
          · exact eq_zero_iff_of_ne_zero hsecond' T.pmg_second_ne_zero
        · refine ⟨.pgg, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
            N c .pgg ?_ ?_ ?_⟩⟩
          · simpa [MultipleReflectionType.latticeForm] using hform
          · exact eq_zero_iff_of_ne_zero hfirst T.pgg_first_ne_zero
          · exact eq_zero_iff_of_ne_zero hsecond T.pgg_second_ne_zero
  | orderTwoCentered =>
      have hfirst : c.firstShiftClass = 0 :=
        firstShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.firstReflectionKind])
      have hsecond : c.secondShiftClass = 0 :=
        secondShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.secondReflectionKind])
      have hfirstModel := model_firstShiftClass_eq_zero_of_centered .cmm (by rfl)
      have hsecondModel := model_secondShiftClass_eq_zero_of_centered .cmm (by rfl)
      refine ⟨.cmm, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
          N c .cmm ?_ ?_ ?_⟩⟩
      · simpa [MultipleReflectionType.latticeForm] using hform
      · exact eq_zero_iff_of_eq_zero hfirst hfirstModel
      · exact eq_zero_iff_of_eq_zero hsecond hsecondModel
  | p3m1 =>
      have hfirst : c.firstShiftClass = 0 :=
        firstShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.firstReflectionKind])
      have hsecond : c.secondShiftClass = 0 :=
        secondShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.secondReflectionKind])
      refine ⟨.p3m1, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
          N c .p3m1 ?_ ?_ ?_⟩⟩
      · simpa [MultipleReflectionType.latticeForm] using hform
      · exact eq_zero_iff_of_eq_zero hfirst
          (model_firstShiftClass_eq_zero_of_centered .p3m1 (by rfl))
      · exact eq_zero_iff_of_eq_zero hsecond
          (model_secondShiftClass_eq_zero_of_centered .p3m1 (by rfl))
  | p31m =>
      have hfirst : c.firstShiftClass = 0 :=
        firstShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.firstReflectionKind])
      have hsecond : c.secondShiftClass = 0 :=
        secondShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.secondReflectionKind])
      refine ⟨.p31m, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
          N c .p31m ?_ ?_ ?_⟩⟩
      · simpa [MultipleReflectionType.latticeForm] using hform
      · exact eq_zero_iff_of_eq_zero hfirst
          (model_firstShiftClass_eq_zero_of_centered .p31m (by rfl))
      · exact eq_zero_iff_of_eq_zero hsecond
          (model_secondShiftClass_eq_zero_of_centered .p31m (by rfl))
  | orderFour =>
      have hsecond : c.secondShiftClass = 0 :=
        secondShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.secondReflectionKind])
      by_cases hfirst : c.firstShiftClass = 0
      · refine ⟨.p4m, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
            N c .p4m ?_ ?_ ?_⟩⟩
        · simpa [MultipleReflectionType.latticeForm] using hform
        · exact eq_zero_iff_of_eq_zero hfirst T.p4m_first_zero
        · exact eq_zero_iff_of_eq_zero hsecond
            (model_secondShiftClass_eq_zero_of_centered .p4m (by rfl))
      · refine ⟨.p4g, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
            N c .p4g ?_ ?_ ?_⟩⟩
        · simpa [MultipleReflectionType.latticeForm] using hform
        · exact eq_zero_iff_of_ne_zero hfirst T.p4g_first_ne_zero
        · exact eq_zero_iff_of_eq_zero hsecond
            (model_secondShiftClass_eq_zero_of_centered .p4g (by rfl))
  | orderSix =>
      have hfirst : c.firstShiftClass = 0 :=
        firstShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.firstReflectionKind])
      have hsecond : c.secondShiftClass = 0 :=
        secondShiftClass_eq_zero_of_centered N c (by
          simp [hform, DihedralLatticeForm.secondReflectionKind])
      refine ⟨.p6m, ⟨multipleReflectionModelIsoOfSameFormAndShiftVanishing
          N c .p6m ?_ ?_ ?_⟩⟩
      · simpa [MultipleReflectionType.latticeForm] using hform
      · exact eq_zero_iff_of_eq_zero hfirst
          (model_firstShiftClass_eq_zero_of_centered .p6m (by rfl))
      · exact eq_zero_iff_of_eq_zero hsecond
          (model_secondShiftClass_eq_zero_of_centered .p6m (by rfl))

/-- The computed primitive shift-status table for the transparent standard models. -/
private theorem modelShiftTable : ModelShiftTable where
  pmm_first_zero := by
    change pmmTwoReflectionData.firstShiftClass = 0
    exact pmmTwoReflectionData_firstShiftClass_eq_zero
  pmm_second_zero := by
    change pmmTwoReflectionData.secondShiftClass = 0
    exact pmmTwoReflectionData_secondShiftClass_eq_zero
  pmg_first_zero := by
    change pmgTwoReflectionData.firstShiftClass = 0
    exact pmgTwoReflectionData_firstShiftClass_eq_zero
  pmg_second_ne_zero := by
    change pmgTwoReflectionData.secondShiftClass ≠ 0
    exact pmgTwoReflectionData_secondShiftClass_ne_zero
  pgg_first_ne_zero := by
    change pggTwoReflectionData.firstShiftClass ≠ 0
    exact pggTwoReflectionData_firstShiftClass_ne_zero
  pgg_second_ne_zero := by
    change pggTwoReflectionData.secondShiftClass ≠ 0
    exact pggTwoReflectionData_secondShiftClass_ne_zero
  p4m_first_zero := by
    change p4mTwoReflectionData.firstShiftClass = 0
    exact p4mTwoReflectionData_firstShiftClass_eq_zero
  p4g_first_ne_zero := by
    change p4gTwoReflectionData.firstShiftClass ≠ 0
    exact p4gTwoReflectionData_firstShiftClass_ne_zero

/-- Every plane group whose point group has multiple reflections is equivalent to one of the
nine transparent multiple-reflection standard models. -/
theorem exists_equivalent_multipleReflectionModel
    (G : PlaneGroup) (hG : PointGroupHasMultipleReflections G) :
    ∃ w : MultipleReflectionType, PlaneGroup.Equivalent G w.model :=
  exists_equivalent_multipleReflectionModel_of_shiftTable modelShiftTable G hG

/-! ## First uniqueness layer for the nine standard models -/

/-- Equivalent multiple-reflection standard models have the same rotation order. -/
theorem MultipleReflectionType.rotationOrder_eq_of_equivalent
    (w v : MultipleReflectionType)
    (h : PlaneGroup.Equivalent w.model v.model) :
    w.rotationOrder = v.rotationOrder := by
  obtain ⟨e⟩ := h
  have hcard := e.pointGroup_natCard_eq
  rw [w.model_pointGroup_card, v.model_pointGroup_card] at hcard
  omega

/-- Standard models with different rotation orders cannot be equivalent. -/
theorem MultipleReflectionType.not_equivalent_of_rotationOrder_ne
    (w v : MultipleReflectionType)
    (horder : w.rotationOrder ≠ v.rotationOrder) :
    ¬ PlaneGroup.Equivalent w.model v.model := by
  intro h
  exact horder (rotationOrder_eq_of_equivalent w v h)

end

end WallpaperGroups
