import WallpaperGroups.Classification.ManyReflections
import WallpaperGroups.Invariants.ReflectionShiftCount

set_option linter.style.header false

/-!
# Intrinsic inequivalence invariants for multiple-reflection models

This file begins the model-side computation of intrinsic invariants used to distinguish the
multiple-reflection wallpaper groups.  The first layer treats the six symmorphic finite-coset
models: every reversing coset has an unshifted pure-linear representative, hence every intrinsic
order-two reflection shift vanishes.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-- A reversing point with an involutive affine lift has vanishing intrinsic reflection shift. -/
theorem reflectionShiftVanishes_of_lift_sq_one
    (G : PlaneGroup) (s : ReversingPoint G)
    (g : G.carrier) (hg : pointProjection G.carrier g = s.1)
    (hg2 : g ^ 2 = 1) :
    reflectionShiftVanishes G s := by
  rw [reflectionShiftVanishes_iff_lift G s g hg]
  rw [shiftClass_eq_zero_iff]
  have hzero : liftPowerFixedTranslation G s.1 2 s.sq g hg = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    change translationPart ((g : EuclideanMotion Plane) ^ 2) = 0
    have hg2' := congrArg Subtype.val hg2
    simpa using congrArg translationPart hg2'
  rw [hzero]
  exact AddSubgroup.zero_mem _

/-- If every finite reflection coset has zero section shift, every reversing point indexed by
any selected dihedral generators has vanishing reflection shift. -/
theorem finiteCoset_zeroSrShift_indexedReversingPoint_vanishes
    {q : ℕ} [NeZero q] (D : FiniteCosetData (DihedralGroup q))
    (d : DihedralGenerators (finiteCosetPlaneGroup D))
    (hrdet : ∀ j : ZMod q,
      LinearMap.det ((D.linearRep (.r j)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hshift : ∀ j : ZMod q, D.shift (.sr j) = 0)
    (i : ZMod d.order.toNat) :
    reflectionShiftVanishes (finiteCosetPlaneGroup D)
      (d.indexedReversingPoint i) := by
  let s := d.indexedReversingPoint i
  have hrange : (s.1 : Plane ≃ₗᵢ[ℝ] Plane) ∈ D.linearRep.range := by
    rw [← finiteCosetPlaneGroup_pointGroup D]
    exact s.1.property
  obtain ⟨p, hp⟩ := hrange
  cases p with
  | r j =>
      have heq : finiteCosetPointElement D (.r j) = s.1 := by
        apply Subtype.ext
        exact hp
      have hpos : finiteCosetPointElement D (.r j) ∈
          orientationPreservingPointGroup (finiteCosetPlaneGroup D) := by
        change 0 < ((pointGroupDet (finiteCosetPlaneGroup D)
          (finiteCosetPointElement D (.r j)) : ℝˣ) : ℝ)
        rw [pointGroupDet_apply, finiteCosetPointElement_coe, hrdet j]
        norm_num
      exact (s.2 (heq ▸ hpos)).elim
  | sr j =>
      have heq : finiteCosetPointElement D (.sr j) = s.1 := by
        apply Subtype.ext
        exact hp
      let g := finiteCosetLift D (.sr j)
      have hg : pointProjection (finiteCosetPlaneGroup D).carrier g = s.1 :=
        (finiteCosetLift_projection D (.sr j)).trans heq
      apply reflectionShiftVanishes_of_lift_sq_one
        (finiteCosetPlaneGroup D) s g hg
      apply Subtype.ext
      change (finiteCosetRepresentative D (.sr j)) ^ 2 = 1
      have hlin : (D.linearRep (.sr j)) ^ 2 = 1 := by
        rw [pow_two, ← map_mul]
        simp
      simp only [finiteCosetRepresentative, hshift j, translation_zero, one_mul]
      change (pureLinear (D.linearRep (.sr j))) ^ 2 = 1
      rw [← map_pow, hlin, map_one]

namespace DihedralGenerators

variable {G : PlaneGroup}

open TwoReflectionExtensionData

/-- The zero finite reflection coordinate is the selected first reflection. -/
@[simp]
theorem indexedReversingPoint_zero_coe (d : DihedralGenerators G) :
    (d.indexedReversingPoint 0).1 = d.reflection := by
  simp [indexedReversingPoint]

/-- The one finite reflection coordinate is the selected adjacent second reflection. -/
@[simp]
theorem indexedReversingPoint_one_coe (d : DihedralGenerators G) :
    (d.indexedReversingPoint 1).1 = d.secondReflection := by
  letI : NeZero d.order.toNat := ⟨by cases d.order <;> decide⟩
  letI : Fact (1 < d.order.toNat) := ⟨by cases d.order <;> decide⟩
  have hval : (1 : ZMod d.order.toNat).val = 1 := by
    rw [ZMod.val_one]
  simp [indexedReversingPoint,
    TwoReflectionExtensionData.pointRotationHom_eq_pow_val,
    DihedralGenerators.secondReflection, hval]

/-- If every finite reversing coordinate vanishes, the intrinsic vanishing count is the
rotation order. -/
theorem vanishingReversingPointCount_eq_orderToNat
    (d : DihedralGenerators G)
    (hvanish : ∀ i : ZMod d.order.toNat,
      reflectionShiftVanishes G (d.indexedReversingPoint i)) :
    vanishingReversingPointCount G = d.order.toNat := by
  rw [d.vanishingReversingPointCount_eq_index_natCard]
  let e : d.VanishingReversingPointIndex ≃ ZMod d.order.toNat :=
    { toFun := fun i => i.1
      invFun := fun i => ⟨i, hvanish i⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  calc
    Nat.card d.VanishingReversingPointIndex = Nat.card (ZMod d.order.toNat) :=
      Nat.card_congr e
    _ = d.order.toNat := Nat.card_zmod d.order.toNat

/-- The zero reflection coordinate has the same intrinsic vanishing status as the first
shift class of any chosen adjacent-lift data. -/
theorem indexedReversingPoint_zero_vanishes_iff_firstShiftClass
    (d : DihedralGenerators G) (c : TwoReflectionExtensionData G d) :
    reflectionShiftVanishes G (d.indexedReversingPoint 0) ↔
      c.firstShiftClass = 0 := by
  let s : ReversingPoint G := ⟨d.reflection, d.reflection_reversing⟩
  have hs : d.indexedReversingPoint 0 = s := by
    apply Subtype.ext
    simp [indexedReversingPoint, s]
  rw [hs]
  simpa [TwoReflectionExtensionData.firstShiftClass] using
    (reflectionShiftVanishes_iff_lift G s c.firstLift c.first_projection)

/-- The one reflection coordinate has the same intrinsic vanishing status as the adjacent
second shift class. -/
theorem indexedReversingPoint_one_vanishes_iff_secondShiftClass
    (d : DihedralGenerators G) (c : TwoReflectionExtensionData G d) :
    reflectionShiftVanishes G (d.indexedReversingPoint 1) ↔
      c.secondShiftClass = 0 := by
  letI : NeZero d.order.toNat := ⟨by cases d.order <;> decide⟩
  letI : Fact (1 < d.order.toNat) := ⟨by cases d.order <;> decide⟩
  have hval : (1 : ZMod d.order.toNat).val = 1 := by
    rw [ZMod.val_one]
  let s : ReversingPoint G :=
    ⟨d.secondReflection, d.secondReflection_reversing⟩
  have hs : d.indexedReversingPoint 1 = s := by
    apply Subtype.ext
    simp [indexedReversingPoint, s,
      TwoReflectionExtensionData.pointRotationHom_eq_pow_val,
      DihedralGenerators.secondReflection, hval]
  rw [hs]
  simpa [TwoReflectionExtensionData.secondShiftClass] using
    (reflectionShiftVanishes_iff_lift G s c.secondLift c.second_projection)

/-- Conjugation by the selected rotation moves reflection coordinate `i` to `i - 2`, so their
intrinsic shift classes vanish simultaneously. -/
theorem indexedReversingPoint_sub_two_vanishes_iff
    (d : DihedralGenerators G) (c : TwoReflectionExtensionData G d)
    (i : ZMod d.order.toNat) :
    reflectionShiftVanishes G (d.indexedReversingPoint i) ↔
      reflectionShiftVanishes G (d.indexedReversingPoint (i - 2)) := by
  letI : NeZero d.order.toNat := ⟨by cases d.order <;> decide⟩
  letI : Fact (1 < d.order.toNat) := ⟨by cases d.order <;> decide⟩
  have hval : (1 : ZMod d.order.toNat).val = 1 := by
    rw [ZMod.val_one]
  have hrword : pointDihedralHom d (.r 1) = d.rotation.1 := by
    rw [pointDihedralHom_r, pointRotationHom_eq_pow_val, hval, pow_one]
  let e := TranslationPreservingIso.inner G c.rotationLift
  have hmap : e.reversingPointEquiv (d.indexedReversingPoint i) =
      d.indexedReversingPoint (i - 2) := by
    apply Subtype.ext
    change e.pointGroupEquiv (pointDihedralHom d (.sr i)) =
      pointDihedralHom d (.sr (i - 2))
    rw [TranslationPreservingIso.inner_pointGroupEquiv,
      c.rotationLift_projection, ← hrword]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    simp
    ring
  simpa [hmap] using
    (e.reflectionShiftVanishes_iff (d.indexedReversingPoint i))

/-- Compute the intrinsic count after replacing vanishing by an explicit predicate on the
canonical finite reflection coordinates. -/
theorem vanishingReversingPointCount_eq_natCard_subtype
    (d : DihedralGenerators G) (P : ZMod d.order.toNat → Prop)
    (hP : ∀ i, reflectionShiftVanishes G (d.indexedReversingPoint i) ↔ P i) :
    vanishingReversingPointCount G =
      Nat.card {i : ZMod d.order.toNat // P i} := by
  rw [d.vanishingReversingPointCount_eq_index_natCard]
  exact Nat.card_congr ((Equiv.refl (ZMod d.order.toNat)).subtypeEquiv hP)

theorem zmod_eq_zero_or_one_of_modulus_eq_two
    {n : ℕ} (hn : n = 2) (i : ZMod n) : i = 0 ∨ i = 1 := by
  letI : NeZero n := ⟨by omega⟩
  have hlt := i.val_lt
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · left
    calc
      i = (i.val : ZMod n) := (ZMod.natCast_zmod_val i).symm
      _ = 0 := by simp [hi]
  · right
    calc
      i = (i.val : ZMod n) := (ZMod.natCast_zmod_val i).symm
      _ = 1 := by simp [hi]

/-- In rotation order two, exactly the first adjacent reflection family vanishing gives
intrinsic vanishing count one. -/
theorem vanishingReversingPointCount_eq_one_of_order_two_first_only
    (d : DihedralGenerators G) (c : TwoReflectionExtensionData G d)
    (horder : d.order = .two)
    (hfirst : c.firstShiftClass = 0)
    (hsecond : c.secondShiftClass ≠ 0) :
    vanishingReversingPointCount G = 1 := by
  classical
  have hn : d.order.toNat = 2 := by
    rw [horder]
    rfl
  letI : Fact (1 < d.order.toNat) := ⟨by omega⟩
  have hone : (1 : ZMod d.order.toNat) ≠ 0 := one_ne_zero
  have hP : ∀ i : ZMod d.order.toNat,
      reflectionShiftVanishes G (d.indexedReversingPoint i) ↔ i = 0 := by
    intro i
    rcases zmod_eq_zero_or_one_of_modulus_eq_two hn i with rfl | rfl
    · simpa [hfirst] using d.indexedReversingPoint_zero_vanishes_iff_firstShiftClass c
    · constructor
      · intro hv
        exact (hsecond
          ((d.indexedReversingPoint_one_vanishes_iff_secondShiftClass c).mp hv)).elim
      · exact fun h => (hone h).elim
  calc
    vanishingReversingPointCount G =
        Nat.card {i : ZMod d.order.toNat // i = 0} :=
      d.vanishingReversingPointCount_eq_natCard_subtype (fun i => i = 0) hP
    _ = 1 := by
      rw [Nat.card_eq_fintype_card]
      simp

/-- In rotation order two, two nonvanishing adjacent reflection families give intrinsic
vanishing count zero. -/
theorem vanishingReversingPointCount_eq_zero_of_order_two
    (d : DihedralGenerators G) (c : TwoReflectionExtensionData G d)
    (horder : d.order = .two)
    (hfirst : c.firstShiftClass ≠ 0)
    (hsecond : c.secondShiftClass ≠ 0) :
    vanishingReversingPointCount G = 0 := by
  classical
  have hn : d.order.toNat = 2 := by
    rw [horder]
    rfl
  letI : NeZero d.order.toNat := ⟨by omega⟩
  have hP : ∀ i : ZMod d.order.toNat,
      reflectionShiftVanishes G (d.indexedReversingPoint i) ↔ False := by
    intro i
    rcases zmod_eq_zero_or_one_of_modulus_eq_two hn i with rfl | rfl
    · simpa [hfirst] using d.indexedReversingPoint_zero_vanishes_iff_firstShiftClass c
    · simpa [hsecond] using d.indexedReversingPoint_one_vanishes_iff_secondShiftClass c
  calc
    vanishingReversingPointCount G =
        Nat.card {i : ZMod d.order.toNat // False} :=
      d.vanishingReversingPointCount_eq_natCard_subtype (fun _ => False) hP
    _ = 0 := by
      rw [Nat.card_eq_fintype_card]
      simp

private theorem zmod_four_cases
    {n : ℕ} (hn : n = 4) (i : ZMod n) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  letI : NeZero n := ⟨by omega⟩
  have hlt := i.val_lt
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hi with hi | hi | hi | hi
  · left
    exact (ZMod.natCast_zmod_val i).symm.trans (by simp [hi])
  · right; left
    exact (ZMod.natCast_zmod_val i).symm.trans (by simp [hi])
  · right; right; left
    exact (ZMod.natCast_zmod_val i).symm.trans (by simp [hi])
  · right; right; right
    exact (ZMod.natCast_zmod_val i).symm.trans (by simp [hi])

private theorem zmod_four_two_sub_two {n : ℕ} (hn : n = 4) :
    (2 : ZMod n) - 2 = 0 := by
  subst n
  decide

private theorem zmod_four_three_sub_two {n : ℕ} (hn : n = 4) :
    (3 : ZMod n) - 2 = 1 := by
  subst n
  decide

private theorem zmod_four_zero_pred_false {n : ℕ} (hn : n = 4) :
    ¬((0 : ZMod n) = 1 ∨ (0 : ZMod n) = 3) := by
  subst n
  decide

private theorem zmod_four_two_pred_false {n : ℕ} (hn : n = 4) :
    ¬((2 : ZMod n) = 1 ∨ (2 : ZMod n) = 3) := by
  subst n
  decide

private theorem zmod_four_pred_natCard {n : ℕ} (hn : n = 4) :
    Nat.card {i : ZMod n // i = 1 ∨ i = 3} = 2 := by
  subst n
  rw [Nat.card_eq_fintype_card]
  decide

/-- In rotation order four, a nonzero first shift and zero adjacent second shift give exactly
two vanishing reversing points, namely the odd reflection coordinates. -/
theorem vanishingReversingPointCount_eq_two_of_order_four
    (d : DihedralGenerators G) (c : TwoReflectionExtensionData G d)
    (horder : d.order = .four)
    (hfirst : c.firstShiftClass ≠ 0)
    (hsecond : c.secondShiftClass = 0) :
    vanishingReversingPointCount G = 2 := by
  classical
  have hn : d.order.toNat = 4 := by
    rw [horder]
    rfl
  letI : NeZero d.order.toNat := ⟨by omega⟩
  have hP : ∀ i : ZMod d.order.toNat,
      reflectionShiftVanishes G (d.indexedReversingPoint i) ↔
        i = 1 ∨ i = 3 := by
    intro i
    rcases zmod_four_cases hn i with rfl | rfl | rfl | rfl
    · constructor
      · intro hv
        exact (hfirst
          ((d.indexedReversingPoint_zero_vanishes_iff_firstShiftClass c).mp hv)).elim
      · intro hp
        exact (zmod_four_zero_pred_false hn hp).elim
    · constructor
      · exact fun _ => Or.inl rfl
      · exact fun _ =>
          (d.indexedReversingPoint_one_vanishes_iff_secondShiftClass c).mpr hsecond
    · have hconj := d.indexedReversingPoint_sub_two_vanishes_iff c 2
      rw [zmod_four_two_sub_two hn] at hconj
      constructor
      · intro hv
        exact (hfirst
          ((d.indexedReversingPoint_zero_vanishes_iff_firstShiftClass c).mp
            (hconj.mp hv))).elim
      · intro hp
        exact (zmod_four_two_pred_false hn hp).elim
    · have hconj := d.indexedReversingPoint_sub_two_vanishes_iff c 3
      rw [zmod_four_three_sub_two hn] at hconj
      constructor
      · exact fun _ => Or.inr rfl
      · exact fun _ => hconj.mpr
          ((d.indexedReversingPoint_one_vanishes_iff_secondShiftClass c).mpr hsecond)
  calc
    vanishingReversingPointCount G =
        Nat.card {i : ZMod d.order.toNat // i = 1 ∨ i = 3} :=
      d.vanishingReversingPointCount_eq_natCard_subtype
        (fun i => i = 1 ∨ i = 3) hP
    _ = 2 := zmod_four_pred_natCard hn

end DihedralGenerators

/-- Every orientation-reversing point action has surjective reflection norm on its fixed
lattice.  This intrinsic predicate distinguishes the centered order-two lattice action from
the primitive rectangular action. -/
def PlaneGroup.AllReversingActionsCentered (G : PlaneGroup) : Prop :=
  ∀ s : pointGroup G.carrier, s ∉ orientationPreservingPointGroup G →
    G.ReflectionActionIsCentered s

/-- Centeredness of all reversing point actions is preserved by a translation-preserving
isomorphism. -/
theorem PlaneGroup.allReversingActionsCentered_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (hG : G.AllReversingActionsCentered) :
    H.AllReversingActionsCentered := by
  intro t ht
  let s : pointGroup G.carrier := e.pointGroupEquiv.symm t
  have hs : s ∉ orientationPreservingPointGroup G := by
    intro hs
    apply ht
    have himage := (e.pointGroupEquiv_mem_orientationPreserving_iff s).2 hs
    simpa [s] using himage
  have hcentered :=
    (PlaneGroup.reflectionActionIsCentered_iff_of_iso e s).mp (hG s hs)
  simpa [s] using hcentered

/-- Centeredness of all reversing point actions is invariant under a
translation-preserving isomorphism. -/
theorem PlaneGroup.allReversingActionsCentered_iff_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H) :
    G.AllReversingActionsCentered ↔ H.AllReversingActionsCentered := by
  constructor
  · exact G.allReversingActionsCentered_of_iso e
  · intro hH
    have hG := H.allReversingActionsCentered_of_iso e.symm hH
    simpa using hG

/-- Zero reflection-coset shifts make the vanishing count equal to the selected dihedral
rotation order. -/
theorem finiteCoset_zeroSrShift_vanishingReversingPointCount
    {q : ℕ} [NeZero q] (D : FiniteCosetData (DihedralGroup q))
    (d : DihedralGenerators (finiteCosetPlaneGroup D))
    (hrdet : ∀ j : ZMod q,
      LinearMap.det ((D.linearRep (.r j)).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (hshift : ∀ j : ZMod q, D.shift (.sr j) = 0) :
    vanishingReversingPointCount (finiteCosetPlaneGroup D) = d.order.toNat :=
  d.vanishingReversingPointCount_eq_orderToNat
    (finiteCoset_zeroSrShift_indexedReversingPoint_vanishes D d hrdet hshift)

@[simp]
theorem pmmModel_vanishingReversingPointCount :
    vanishingReversingPointCount pmmModel = 2 := by
  simpa [pmmModel, pmmDihedralGenerators, finiteCosetDihedralGenerators,
    DihedralRotationOrder.toNat] using
    finiteCoset_zeroSrShift_vanishingReversingPointCount
      pmmCosetData pmmDihedralGenerators
      (by intro i; simp [pmmCosetData, symmorphicDihedralCosetData])
      (by intro i; rfl)

@[simp]
theorem cmmModel_vanishingReversingPointCount :
    vanishingReversingPointCount cmmModel = 2 := by
  simpa [cmmModel, cmmDihedralGenerators, finiteCosetDihedralGenerators,
    DihedralRotationOrder.toNat] using
    finiteCoset_zeroSrShift_vanishingReversingPointCount
      cmmCosetData cmmDihedralGenerators
      (by intro i; simp [cmmCosetData, symmorphicDihedralCosetData])
      (by intro i; rfl)

@[simp]
theorem p3m1Model_vanishingReversingPointCount :
    vanishingReversingPointCount p3m1Model = 3 := by
  simpa [p3m1Model, p3m1DihedralGenerators, finiteCosetDihedralGenerators,
    DihedralRotationOrder.toNat] using
    finiteCoset_zeroSrShift_vanishingReversingPointCount
      p3m1CosetData p3m1DihedralGenerators
      (by intro i; simp [p3m1CosetData, symmorphicDihedralCosetData])
      (by intro i; rfl)

@[simp]
theorem p31mModel_vanishingReversingPointCount :
    vanishingReversingPointCount p31mModel = 3 := by
  simpa [p31mModel, p31mDihedralGenerators, finiteCosetDihedralGenerators,
    DihedralRotationOrder.toNat] using
    finiteCoset_zeroSrShift_vanishingReversingPointCount
      p31mCosetData p31mDihedralGenerators
      (by intro i; simp [p31mCosetData, twistedSymmorphicDihedralCosetData])
      (by intro i; rfl)

@[simp]
theorem p4mModel_vanishingReversingPointCount :
    vanishingReversingPointCount p4mModel = 4 := by
  simpa [p4mModel, p4mDihedralGenerators, finiteCosetDihedralGenerators,
    DihedralRotationOrder.toNat] using
    finiteCoset_zeroSrShift_vanishingReversingPointCount
      p4mCosetData p4mDihedralGenerators
      (by intro i; simp [p4mCosetData, symmorphicDihedralCosetData])
      (by intro i; rfl)

@[simp]
theorem p6mModel_vanishingReversingPointCount :
    vanishingReversingPointCount p6mModel = 6 := by
  simpa [p6mModel, p6mDihedralGenerators, finiteCosetDihedralGenerators,
    DihedralRotationOrder.toNat] using
    finiteCoset_zeroSrShift_vanishingReversingPointCount
      p6mCosetData p6mDihedralGenerators
      (by intro i; simp [p6mCosetData, symmorphicDihedralCosetData])
      (by intro i; rfl)

@[simp]
theorem pmgModel_vanishingReversingPointCount :
    vanishingReversingPointCount pmgModel = 1 :=
  pmgDihedralGenerators.vanishingReversingPointCount_eq_one_of_order_two_first_only
    pmgTwoReflectionData rfl
    pmgTwoReflectionData_firstShiftClass_eq_zero
    pmgTwoReflectionData_secondShiftClass_ne_zero

@[simp]
theorem pggModel_vanishingReversingPointCount :
    vanishingReversingPointCount pggModel = 0 :=
  pggDihedralGenerators.vanishingReversingPointCount_eq_zero_of_order_two
    pggTwoReflectionData rfl
    pggTwoReflectionData_firstShiftClass_ne_zero
    pggTwoReflectionData_secondShiftClass_ne_zero

@[simp]
theorem p4gModel_vanishingReversingPointCount :
    vanishingReversingPointCount p4gModel = 2 :=
  p4gDihedralGenerators.vanishingReversingPointCount_eq_two_of_order_four
    p4gTwoReflectionData rfl
    p4gTwoReflectionData_firstShiftClass_ne_zero
    p4gTwoReflectionData_secondShiftClass_eq_zero

/-! ## The intrinsic centered/primitive separator in rotation order two -/

/-- Both reversing point actions of the centered order-two `cmm` model are centered. -/
theorem cmmModel_allReversingActionsCentered :
    cmmModel.AllReversingActionsCentered := by
  intro s hs
  let x : ReversingPoint cmmModel := ⟨s, hs⟩
  obtain ⟨i, hi⟩ :=
    cmmDihedralGenerators.indexedReversingPoint_surjective x
  have hn : cmmDihedralGenerators.order.toNat = 2 := rfl
  rcases DihedralGenerators.zmod_eq_zero_or_one_of_modulus_eq_two hn i with rfl | rfl
  · have hsref : s = cmmDihedralGenerators.reflection := by
      simpa [x] using congrArg Subtype.val hi.symm
    rw [hsref]
    apply cmmDihedralNormalForm.firstReflection_centered_of_matrix
    rw [show cmmDihedralNormalForm.form = .orderTwoCentered by rfl]
    exact matrixReflectionIsCentered_orderTwoCentered_first
  · have hsref : s = cmmDihedralGenerators.secondReflection := by
      simpa [x] using congrArg Subtype.val hi.symm
    rw [hsref]
    apply cmmDihedralNormalForm.secondReflection_centered_of_matrix
    rw [show cmmDihedralNormalForm.form = .orderTwoCentered by rfl]
    exact matrixReflectionIsCentered_orderTwoCentered_second

/-- The primitive order-two `pmm` model has a reversing point action which is not centered. -/
theorem pmmModel_not_allReversingActionsCentered :
    ¬ pmmModel.AllReversingActionsCentered := by
  intro hcentered
  apply pmmDihedralNormalForm.firstReflection_not_centered_of_matrix
    (by
      rw [show pmmDihedralNormalForm.form = .orderTwoPrimitive by rfl]
      exact not_matrixReflectionIsCentered_orderTwoPrimitive_first)
  exact hcentered pmmDihedralGenerators.reflection
    pmmDihedralGenerators.reflection_reversing

/-- The centered and primitive order-two lattice actions are intrinsically inequivalent. -/
theorem cmmModel_not_equivalent_pmmModel :
    ¬ PlaneGroup.Equivalent cmmModel pmmModel := by
  rintro ⟨e⟩
  apply pmmModel_not_allReversingActionsCentered
  exact (PlaneGroup.allReversingActionsCentered_iff_of_iso e).mp
    cmmModel_allReversingActionsCentered

/-- The two order-three lattice embeddings are intrinsically inequivalent. -/
theorem p3m1Model_not_equivalent_p31mModel :
    ¬ PlaneGroup.Equivalent p3m1Model p31mModel :=
  PlaneGroup.DihedralLatticeNormalForm.p3m1_not_equivalent_p31m
    p3m1DihedralNormalForm rfl p31mDihedralNormalForm rfl

/-- Exchanging the two order-two `pmg` reflection generators exchanges exactly the two
quotient-valued vanishing tests. -/
theorem pmgGeneratorSwap_identifies_asymmetricCases :
    ((pmgTwoReflectionData.swapOrderTwo rfl).firstShiftClass = 0 ↔
        pmgTwoReflectionData.secondShiftClass = 0) ∧
      ((pmgTwoReflectionData.swapOrderTwo rfl).secondShiftClass = 0 ↔
        pmgTwoReflectionData.firstShiftClass = 0) := by
  constructor
  · exact TwoReflectionExtensionData.swapOrderTwo_firstShiftClass_eq_zero_iff
      pmgTwoReflectionData rfl
  · exact TwoReflectionExtensionData.swapOrderTwo_secondShiftClass_eq_zero_iff
      pmgTwoReflectionData rfl

/-- Every standard model in the nine-label family really lies in the multiple-reflection
sector. -/
theorem multipleReflectionModel_hasMultipleReflections
    (w : MultipleReflectionType) :
    PointGroupHasMultipleReflections w.model :=
  (multipleReflectionModelData w).d.pointGroupHasMultipleReflections

/-! ## Pairwise inequivalence and the nine-class theorem -/

namespace MultipleReflectionType

/-- The intrinsic number of reversing point elements with vanishing shift for each standard
multiple-reflection label. -/
def vanishingCount : MultipleReflectionType → ℕ
  | .cmm | .pmm => 2
  | .pmg => 1
  | .pgg => 0
  | .p3m1 | .p31m => 3
  | .p4m => 4
  | .p4g => 2
  | .p6m => 6

/-- Computation of the intrinsic vanishing count on all nine standard models. -/
@[simp]
theorem model_vanishingReversingPointCount (w : MultipleReflectionType) :
    vanishingReversingPointCount w.model = w.vanishingCount := by
  cases w <;> simp [MultipleReflectionType.model, vanishingCount]

/-- Equivalent standard models have the same intrinsic vanishing count. -/
theorem vanishingCount_eq_of_models_equivalent
    (w v : MultipleReflectionType)
    (h : PlaneGroup.Equivalent w.model v.model) :
    w.vanishingCount = v.vanishingCount := by
  obtain ⟨e⟩ := h
  calc
    w.vanishingCount = vanishingReversingPointCount w.model :=
      w.model_vanishingReversingPointCount.symm
    _ = vanishingReversingPointCount v.model :=
      e.vanishingReversingPointCount_eq
    _ = v.vanishingCount := v.model_vanishingReversingPointCount

/-- Equivalent multiple-reflection standard models carry the same label. -/
theorem eq_of_models_equivalent
    (w v : MultipleReflectionType)
    (h : PlaneGroup.Equivalent w.model v.model) :
    w = v := by
  have horder := w.rotationOrder_eq_of_equivalent v h
  have hcount := w.vanishingCount_eq_of_models_equivalent v h
  cases w <;> cases v
  all_goals try rfl
  all_goals try { simp [MultipleReflectionType.rotationOrder] at horder }
  all_goals try { simp [vanishingCount] at hcount }
  · exact (cmmModel_not_equivalent_pmmModel h).elim
  · exact (cmmModel_not_equivalent_pmmModel
      (PlaneGroup.Equivalent.symm h)).elim
  · exact (p3m1Model_not_equivalent_p31mModel h).elim
  · exact (p3m1Model_not_equivalent_p31mModel
      (PlaneGroup.Equivalent.symm h)).elim

/-- Two multiple-reflection standard models are equivalent exactly when their labels agree. -/
theorem models_equivalent_iff (w v : MultipleReflectionType) :
    PlaneGroup.Equivalent w.model v.model ↔ w = v := by
  constructor
  · exact w.eq_of_models_equivalent v
  · rintro rfl
    exact PlaneGroup.Equivalent.refl _

/-- Distinct multiple-reflection labels give inequivalent standard models. -/
theorem not_equivalent_of_ne
    (w v : MultipleReflectionType) (h : w ≠ v) :
    ¬ PlaneGroup.Equivalent w.model v.model := by
  intro he
  exact h ((w.models_equivalent_iff v).mp he)

/-- There are exactly nine labels in the multiple-reflection sector. -/
@[simp]
theorem fintype_card_eq_nine : Fintype.card MultipleReflectionType = 9 := by
  decide

/-- `Nat.card` form of the nine-label cardinality computation. -/
@[simp]
theorem card_eq_nine : Nat.card MultipleReflectionType = 9 := by
  rw [Nat.card_eq_fintype_card]
  exact fintype_card_eq_nine

end MultipleReflectionType

/-- Every plane group with multiple point-group reflections has a unique standard label. -/
theorem classify_multiple_reflections
    (G : PlaneGroup) (hG : PointGroupHasMultipleReflections G) :
    ∃! w : MultipleReflectionType, PlaneGroup.Equivalent G w.model := by
  obtain ⟨w, hw⟩ := exists_equivalent_multipleReflectionModel G hG
  refine ⟨w, hw, ?_⟩
  intro v hv
  exact (v.models_equivalent_iff w).mp
    (PlaneGroup.Equivalent.trans (PlaneGroup.Equivalent.symm hv) hw)

end

end WallpaperGroups
