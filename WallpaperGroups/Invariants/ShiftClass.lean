import WallpaperGroups.Presentations.CyclicExtension

set_option linter.style.header false

/-!
# Quotient-valued finite shift classes

For a finite-order point element `h` and a lift `g`, the full-period power `g ^ q` is a
translation fixed by `h`.  Replacing the lift changes that translation by the finite norm
`1 + h + ⋯ + h^(q-1)`.  This module therefore records the invariant in the canonical quotient
`T^h / N_h(T)`, proves lift independence, and transports it through translation-preserving
isomorphisms.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion
open scoped BigOperators

noncomputable section

/-- The finite norm for the action of a point-group element on translation vectors. -/
def finiteNormHom (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ) :
    translationVectors G.carrier →+ translationVectors G.carrier :=
  ∑ i ∈ Finset.range q, (pointAction G.carrier (h ^ i)).toAddMonoidHom

/-- Evaluating the finite norm is the corresponding finite orbit sum. -/
@[simp]
theorem finiteNormHom_apply (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (t : translationVectors G.carrier) :
    finiteNormHom G h q t = ∑ i ∈ Finset.range q, pointAction G.carrier (h ^ i) t := by
  simp [finiteNormHom]

/-- Coercing a finite norm to the plane gives the ambient finite orbit sum. -/
theorem finiteNormHom_coe (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (t : translationVectors G.carrier) :
    ((finiteNormHom G h q t : translationVectors G.carrier) : Plane) =
      ∑ i ∈ Finset.range q,
        ((h ^ i : pointGroup G.carrier) : Plane ≃ₗᵢ[ℝ] Plane) (t : Plane) := by
  rw [finiteNormHom_apply]
  exact map_sum (translationVectors G.carrier).subtype _ _

/-- A finite norm is fixed when the acting point element has the selected finite order. -/
theorem finiteNormHom_fixed (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) (t : translationVectors G.carrier) :
    pointAction G.carrier h (finiteNormHom G h q t) = finiteNormHom G h q t := by
  rw [finiteNormHom_apply]
  rw [map_sum]
  have hsum :
      (∑ i ∈ Finset.range q, pointAction G.carrier (h * h ^ i) t) + t =
        (∑ i ∈ Finset.range q, pointAction G.carrier (h ^ i) t) +
          pointAction G.carrier (h ^ q) t := by
    simp_rw [← pow_succ']
    conv_lhs =>
      rhs
      rw [← pointAction_one G.carrier t]
    change
      (∑ i ∈ Finset.range q, pointAction G.carrier (h ^ (i + 1)) t) +
          pointAction G.carrier (h ^ 0) t =
        (∑ i ∈ Finset.range q, pointAction G.carrier (h ^ i) t) +
          pointAction G.carrier (h ^ q) t
    exact (Finset.sum_range_succ'
      (fun i => pointAction G.carrier (h ^ i) t) q).symm.trans
        (Finset.sum_range_succ (fun i => pointAction G.carrier (h ^ i) t) q)
  rw [hq, pointAction_one] at hsum
  exact add_right_cancel hsum

/-- Translation vectors fixed by a selected point-group element. -/
def fixedTranslationSubgroup (G : PlaneGroup) (h : pointGroup G.carrier) :
    AddSubgroup (translationVectors G.carrier) where
  carrier := {t | pointAction G.carrier h t = t}
  zero_mem' := by simp
  add_mem' := by
    intro t u ht hu
    change pointAction G.carrier h t = t at ht
    change pointAction G.carrier h u = u at hu
    change pointAction G.carrier h (t + u) = t + u
    rw [map_add, ht, hu]
  neg_mem' := by
    intro t ht
    change pointAction G.carrier h t = t at ht
    change pointAction G.carrier h (-t) = -t
    rw [map_neg, ht]

/-- The finite norm, with codomain restricted to the fixed translations. -/
def finiteNormFixedHom (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) :
    translationVectors G.carrier →+ fixedTranslationSubgroup G h where
  toFun t := ⟨finiteNormHom G h q t, finiteNormHom_fixed G h q hq t⟩
  map_zero' := by ext; simp
  map_add' t u := by
    apply Subtype.ext
    exact (finiteNormHom G h q).map_add t u

/-- Norm translations inside the fixed translation subgroup. -/
def normTranslationSubgroup (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) : AddSubgroup (fixedTranslationSubgroup G h) :=
  (finiteNormFixedHom G h q hq).range

/-- The quotient-valued shift group `T^h / N_h(T)`. -/
abbrev ShiftClassGroup (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) :=
  fixedTranslationSubgroup G h ⧸ normTranslationSubgroup G h q hq

/-! ## Lift powers and independence -/

/-- The translation part of a power is the finite orbit sum of the original translation part. -/
theorem translationPart_pow_eq_sum (g : EuclideanMotion Plane) (q : ℕ) :
    translationPart (g ^ q) =
      ∑ i ∈ Finset.range q, ((linearPart g) ^ i) (translationPart g) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [pow_succ, translationPart_mul, ih, map_pow]
      simpa using (Finset.sum_range_succ
        (fun i => ((linearPart g) ^ i) (translationPart g)) q).symm

/-- Left-multiplying a lift by translation changes its full-period translation by the norm. -/
theorem translationPart_translation_mul_pow
    (g : EuclideanMotion Plane) (t : Plane) (q : ℕ) :
    translationPart ((translation t * g) ^ q) =
      (∑ i ∈ Finset.range q, ((linearPart g) ^ i) t) + translationPart (g ^ q) := by
  rw [translationPart_pow_eq_sum, translationPart_pow_eq_sum]
  simp only [linearPart_mul, linearPart_translation, one_mul, translationPart_mul,
    translationPart_translation]
  simp_rw [map_add]
  exact Finset.sum_add_distrib

/-- The full-period translation vector of a lift. -/
def liftPowerTranslation (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) (g : G.carrier) (hg : pointProjection G.carrier g = h) :
    translationVectors G.carrier :=
  ⟨translationPart ((g : EuclideanMotion Plane) ^ q), by
    apply lift_pow_translationPart_mem G.carrier g q
    simpa [hg] using hq⟩

/-- The lift-power translation, bundled with its point-action fixedness. -/
def liftPowerFixedTranslation (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) (g : G.carrier) (hg : pointProjection G.carrier g = h) :
    fixedTranslationSubgroup G h :=
  ⟨liftPowerTranslation G h q hq g hg, by
    change pointAction G.carrier h (liftPowerTranslation G h q hq g hg) =
      liftPowerTranslation G h q hq g hg
    apply Subtype.ext
    change (h : Plane ≃ₗᵢ[ℝ] Plane)
        (translationPart ((g : EuclideanMotion Plane) ^ q)) =
      translationPart ((g : EuclideanMotion Plane) ^ q)
    rw [← hg]
    exact lift_pow_translationPart_fixed G.carrier g q (by simpa [hg] using hq)⟩

/-- The canonical quotient-valued shift class of a finite-order point lift. -/
def shiftClass (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) (g : G.carrier) (hg : pointProjection G.carrier g = h) :
    ShiftClassGroup G h q hq :=
  QuotientAddGroup.mk' (normTranslationSubgroup G h q hq)
    (liftPowerFixedTranslation G h q hq g hg)

/-- Equality of two quotient representatives is witnessed by adding a finite norm.  The chosen
sign convention is `x = N_h(t) + y`. -/
theorem shiftClass_mk_eq_mk_iff_exists_norm_add
    (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ) (hq : h ^ q = 1)
    (x y : fixedTranslationSubgroup G h) :
    QuotientAddGroup.mk' (normTranslationSubgroup G h q hq) x =
        QuotientAddGroup.mk' (normTranslationSubgroup G h q hq) y ↔
      ∃ t : translationVectors G.carrier, x = finiteNormFixedHom G h q hq t + y := by
  change (x : ShiftClassGroup G h q hq) = (y : ShiftClassGroup G h q hq) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    abel
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    abel

/-- Equality of two lift shift classes is equivalently an explicit finite-norm difference of
their fixed power translations. -/
theorem shiftClass_eq_iff_exists_norm_add
    (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ) (hq : h ^ q = 1)
    (g k : G.carrier) (hg : pointProjection G.carrier g = h)
    (hk : pointProjection G.carrier k = h) :
    shiftClass G h q hq g hg = shiftClass G h q hq k hk ↔
      ∃ t : translationVectors G.carrier,
        liftPowerFixedTranslation G h q hq g hg =
          finiteNormFixedHom G h q hq t + liftPowerFixedTranslation G h q hq k hk :=
  shiftClass_mk_eq_mk_iff_exists_norm_add G h q hq _ _

/-- The translation relating two lifts of the same point element. -/
def liftDifferenceTranslation (G : PlaneGroup) (h : pointGroup G.carrier)
    (g k : G.carrier) (hg : pointProjection G.carrier g = h)
    (hk : pointProjection G.carrier k = h) : translationVectors G.carrier :=
  ⟨translationPart ((k : EuclideanMotion Plane) * (g : EuclideanMotion Plane)⁻¹), by
    change translation
        (translationPart ((k : EuclideanMotion Plane) * (g : EuclideanMotion Plane)⁻¹)) ∈
      G.carrier
    rw [← eq_translation_of_linearPart_eq_one]
    · exact G.carrier.mul_mem k.property (G.carrier.inv_mem g.property)
    · rw [linearPart_mul, linearPart_inv]
      have hlinear : linearPart (k : EuclideanMotion Plane) =
          linearPart (g : EuclideanMotion Plane) := by
        simpa only [pointProjection_coe] using congrArg Subtype.val (hk.trans hg.symm)
      rw [hlinear, mul_inv_cancel]⟩

/-- Reconstruct the second lift by left translation from the first. -/
theorem translation_liftDifference_mul
    (G : PlaneGroup) (h : pointGroup G.carrier)
    (g k : G.carrier) (hg : pointProjection G.carrier g = h)
    (hk : pointProjection G.carrier k = h) :
    translation (liftDifferenceTranslation G h g k hg hk : Plane) *
        (g : EuclideanMotion Plane) = (k : EuclideanMotion Plane) := by
  unfold liftDifferenceTranslation
  rw [← eq_translation_of_linearPart_eq_one]
  · group
  · rw [linearPart_mul, linearPart_inv]
    have hlinear : linearPart (k : EuclideanMotion Plane) =
        linearPart (g : EuclideanMotion Plane) := by
      simpa only [pointProjection_coe] using congrArg Subtype.val (hk.trans hg.symm)
    rw [hlinear, mul_inv_cancel]

/-- The difference of the power translations of two lifts is a finite norm. -/
theorem liftPowerTranslation_sub_eq_norm
    (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ) (hq : h ^ q = 1)
    (g k : G.carrier) (hg : pointProjection G.carrier g = h)
    (hk : pointProjection G.carrier k = h) :
    liftPowerTranslation G h q hq k hk - liftPowerTranslation G h q hq g hg =
      finiteNormHom G h q (liftDifferenceTranslation G h g k hg hk) := by
  apply Subtype.ext
  change translationPart ((k : EuclideanMotion Plane) ^ q) -
      translationPart ((g : EuclideanMotion Plane) ^ q) =
    ((finiteNormHom G h q (liftDifferenceTranslation G h g k hg hk) :
      translationVectors G.carrier) : Plane)
  rw [← translation_liftDifference_mul G h g k hg hk,
    translationPart_translation_mul_pow]
  rw [finiteNormHom_coe]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro i hi
  have hlinear : linearPart (g : EuclideanMotion Plane) = (h : Plane ≃ₗᵢ[ℝ] Plane) := by
    simpa only [pointProjection_coe] using congrArg Subtype.val hg
  rw [hlinear]
  rfl

/-- The quotient-valued shift class is independent of the selected lift. -/
theorem shiftClass_lift_independent
    (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ) (hq : h ^ q = 1)
    (g k : G.carrier) (hg : pointProjection G.carrier g = h)
    (hk : pointProjection G.carrier k = h) :
    shiftClass G h q hq g hg = shiftClass G h q hq k hk := by
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  change liftPowerFixedTranslation G h q hq g hg -
      liftPowerFixedTranslation G h q hq k hk ∈
    normTranslationSubgroup G h q hq
  refine ⟨-liftDifferenceTranslation G h g k hg hk, ?_⟩
  apply Subtype.ext
  change finiteNormHom G h q (-liftDifferenceTranslation G h g k hg hk) =
    liftPowerTranslation G h q hq g hg - liftPowerTranslation G h q hq k hk
  rw [(finiteNormHom G h q).map_neg]
  rw [← liftPowerTranslation_sub_eq_norm G h q hq g k hg hk]
  abel

/-! ## Transport under translation-preserving isomorphisms -/

/-! ### Transport from an arbitrary intertwining lattice equivalence -/

/-- An additive equivalence which intertwines two selected point actions maps the corresponding
fixed translation subgroups onto one another. -/
theorem fixedTranslationSubgroup_map_of_intertwining
    {G H : PlaneGroup}
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hG : pointGroup G.carrier) (hH : pointGroup H.carrier)
    (heq : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier hG t) = pointAction H.carrier hH (eT t)) :
    (fixedTranslationSubgroup G hG).map eT.toAddMonoidHom =
      fixedTranslationSubgroup H hH := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    change pointAction H.carrier hH (eT t) = eT t
    rw [← heq]
    change pointAction G.carrier hG t = t at ht
    rw [ht]
  · intro hu
    refine ⟨eT.symm u, ?_, by simp⟩
    change pointAction G.carrier hG (eT.symm u) = eT.symm u
    apply eT.injective
    rw [heq, eT.apply_symm_apply]
    change pointAction H.carrier hH u = u at hu
    exact hu

/-- The fixed-subgroup equivalence induced by an arbitrary additive action intertwiner. -/
def fixedTranslationEquivOfIntertwining
    {G H : PlaneGroup}
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hG : pointGroup G.carrier) (hH : pointGroup H.carrier)
    (heq : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier hG t) = pointAction H.carrier hH (eT t)) :
    fixedTranslationSubgroup G hG ≃+ fixedTranslationSubgroup H hH :=
  (eT.addSubgroupMap (fixedTranslationSubgroup G hG)).trans
    (AddEquiv.addSubgroupCongr
      (fixedTranslationSubgroup_map_of_intertwining eT hG hH heq))

/-- On representatives, the fixed-subgroup equivalence is the original additive equivalence. -/
@[simp]
theorem fixedTranslationEquivOfIntertwining_coe
    {G H : PlaneGroup}
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hG : pointGroup G.carrier) (hH : pointGroup H.carrier)
    (heq : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier hG t) = pointAction H.carrier hH (eT t))
    (t : fixedTranslationSubgroup G hG) :
    ((fixedTranslationEquivOfIntertwining eT hG hH heq t :
      fixedTranslationSubgroup H hH) : translationVectors H.carrier) =
        eT (t : translationVectors G.carrier) :=
  rfl

/-- Intertwining one selected action implies intertwining each of its natural-number powers. -/
theorem pointAction_pow_intertwining
    {G H : PlaneGroup}
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hG : pointGroup G.carrier) (hH : pointGroup H.carrier)
    (heq : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier hG t) = pointAction H.carrier hH (eT t))
    (i : ℕ) (t : translationVectors G.carrier) :
    eT (pointAction G.carrier (hG ^ i) t) =
      pointAction H.carrier (hH ^ i) (eT t) := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
      rw [pow_succ, pointAction_mul, pow_succ, pointAction_mul]
      rw [ih, heq]

/-- An arbitrary additive action intertwiner commutes with the associated finite norm maps. -/
theorem finiteNormHom_natural_of_intertwining
    {G H : PlaneGroup}
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hG : pointGroup G.carrier) (hH : pointGroup H.carrier)
    (heq : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier hG t) = pointAction H.carrier hH (eT t))
    (q : ℕ) (t : translationVectors G.carrier) :
    eT (finiteNormHom G hG q t) = finiteNormHom H hH q (eT t) := by
  rw [finiteNormHom_apply, finiteNormHom_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact pointAction_pow_intertwining eT hG hH heq i t

/-- The fixed-subgroup equivalence induced by an action intertwiner maps the finite norm range
onto the target finite norm range. -/
theorem normTranslationSubgroup_map_of_intertwining
    {G H : PlaneGroup}
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hG : pointGroup G.carrier) (hH : pointGroup H.carrier)
    (heq : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier hG t) = pointAction H.carrier hH (eT t))
    (q : ℕ) (hqG : hG ^ q = 1) (hqH : hH ^ q = 1) :
    (normTranslationSubgroup G hG q hqG).map
        (fixedTranslationEquivOfIntertwining eT hG hH heq).toAddMonoidHom =
      normTranslationSubgroup H hH q hqH := by
  ext u
  constructor
  · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
    refine ⟨eT t, ?_⟩
    apply Subtype.ext
    change finiteNormHom H hH q (eT t) = eT (finiteNormHom G hG q t)
    exact (finiteNormHom_natural_of_intertwining eT hG hH heq q t).symm
  · rintro ⟨t, rfl⟩
    let s : translationVectors G.carrier := eT.symm t
    let x : fixedTranslationSubgroup G hG := finiteNormFixedHom G hG q hqG s
    refine ⟨x, ⟨s, rfl⟩, ?_⟩
    apply Subtype.ext
    change eT (finiteNormHom G hG q s) = finiteNormHom H hH q t
    calc
      eT (finiteNormHom G hG q s) = finiteNormHom H hH q (eT s) :=
        finiteNormHom_natural_of_intertwining eT hG hH heq q s
      _ = finiteNormHom H hH q t := by simp [s]

/-- An additive equivalence intertwining selected finite point actions induces an equivalence of
their quotient-valued shift groups. -/
def shiftClassEquivOfIntertwining
    {G H : PlaneGroup}
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hG : pointGroup G.carrier) (hH : pointGroup H.carrier)
    (heq : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier hG t) = pointAction H.carrier hH (eT t))
    (q : ℕ) (hqG : hG ^ q = 1) (hqH : hH ^ q = 1) :
    ShiftClassGroup G hG q hqG ≃+ ShiftClassGroup H hH q hqH :=
  QuotientAddGroup.congr
    (normTranslationSubgroup G hG q hqG)
    (normTranslationSubgroup H hH q hqH)
    (fixedTranslationEquivOfIntertwining eT hG hH heq)
    (normTranslationSubgroup_map_of_intertwining eT hG hH heq q hqG hqH)

/-- The shift-group equivalence induced by an action intertwiner maps a quotient representative
to the class of its image fixed translation. -/
@[simp]
theorem shiftClassEquivOfIntertwining_mk
    {G H : PlaneGroup}
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hG : pointGroup G.carrier) (hH : pointGroup H.carrier)
    (heq : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier hG t) = pointAction H.carrier hH (eT t))
    (q : ℕ) (hqG : hG ^ q = 1) (hqH : hH ^ q = 1)
    (x : fixedTranslationSubgroup G hG) :
    shiftClassEquivOfIntertwining eT hG hH heq q hqG hqH
        (QuotientAddGroup.mk' (normTranslationSubgroup G hG q hqG) x) =
      QuotientAddGroup.mk' (normTranslationSubgroup H hH q hqH)
        (fixedTranslationEquivOfIntertwining eT hG hH heq x) :=
  rfl

/-- The finite-order proof transported to the target point group. -/
theorem transportedPointPowerProof {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) (q : ℕ) (hq : h ^ q = 1) :
    (e.pointGroupEquiv h) ^ q = 1 := by
  rw [← map_pow, hq, map_one]

/-- A translation-preserving isomorphism maps fixed translations to fixed translations. -/
theorem fixedTranslationSubgroup_map {G H : PlaneGroup}
    (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) :
    (fixedTranslationSubgroup G h).map e.translationVectorEquiv.toAddMonoidHom =
      fixedTranslationSubgroup H (e.pointGroupEquiv h) := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    change pointAction H.carrier (e.pointGroupEquiv h) (e.translationVectorEquiv t) =
      e.translationVectorEquiv t
    rw [← e.translationVector_pointAction]
    change pointAction G.carrier h t = t at ht
    rw [ht]
  · intro hu
    refine ⟨e.translationVectorEquiv.symm u, ?_, by simp⟩
    change pointAction G.carrier h (e.translationVectorEquiv.symm u) =
      e.translationVectorEquiv.symm u
    apply e.translationVectorEquiv.injective
    rw [e.translationVector_pointAction, e.translationVectorEquiv.apply_symm_apply]
    change pointAction H.carrier (e.pointGroupEquiv h) u = u at hu
    exact hu

/-- The induced equivalence between the fixed translation subgroups. -/
def fixedTranslationEquiv {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) :
    fixedTranslationSubgroup G h ≃+ fixedTranslationSubgroup H (e.pointGroupEquiv h) :=
  (e.translationVectorEquiv.addSubgroupMap (fixedTranslationSubgroup G h)).trans
    (AddEquiv.addSubgroupCongr (fixedTranslationSubgroup_map e h))

/-- The fixed-translation equivalence is the induced translation-vector equivalence on values. -/
@[simp]
theorem fixedTranslationEquiv_coe {G H : PlaneGroup}
    (e : TranslationPreservingIso G H) (h : pointGroup G.carrier)
    (t : fixedTranslationSubgroup G h) :
    ((fixedTranslationEquiv e h t : fixedTranslationSubgroup H (e.pointGroupEquiv h)) :
      translationVectors H.carrier) = e.translationVectorEquiv (t : translationVectors G.carrier) :=
  rfl

/-- The induced translation equivalence intertwines finite norm maps. -/
theorem finiteNormHom_natural {G H : PlaneGroup}
    (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) (q : ℕ)
    (t : translationVectors G.carrier) :
    e.translationVectorEquiv (finiteNormHom G h q t) =
      finiteNormHom H (e.pointGroupEquiv h) q (e.translationVectorEquiv t) := by
  rw [finiteNormHom_apply, finiteNormHom_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    e.translationVectorEquiv (pointAction G.carrier (h ^ i) t) =
        pointAction H.carrier (e.pointGroupEquiv (h ^ i))
          (e.translationVectorEquiv t) := e.translationVector_pointAction (h ^ i) t
    _ = pointAction H.carrier ((e.pointGroupEquiv h) ^ i)
          (e.translationVectorEquiv t) := by rw [map_pow]

/-- The equivalence on fixed translations maps the norm image onto the target norm image. -/
theorem normTranslationSubgroup_map {G H : PlaneGroup}
    (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) :
    (normTranslationSubgroup G h q hq).map (fixedTranslationEquiv e h).toAddMonoidHom =
      normTranslationSubgroup H (e.pointGroupEquiv h) q
        (transportedPointPowerProof e h q hq) := by
  ext u
  constructor
  · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
    refine ⟨e.translationVectorEquiv t, ?_⟩
    apply Subtype.ext
    change finiteNormHom H (e.pointGroupEquiv h) q (e.translationVectorEquiv t) =
      e.translationVectorEquiv (finiteNormHom G h q t)
    exact (finiteNormHom_natural e h q t).symm
  · rintro ⟨t, rfl⟩
    let s : translationVectors G.carrier := e.translationVectorEquiv.symm t
    let x : fixedTranslationSubgroup G h := finiteNormFixedHom G h q hq s
    refine ⟨x, ⟨s, rfl⟩, ?_⟩
    apply Subtype.ext
    change e.translationVectorEquiv (finiteNormHom G h q s) =
      finiteNormHom H (e.pointGroupEquiv h) q t
    rw [finiteNormHom_natural]
    simp [s]

/-- Translation-preserving isomorphisms induce equivalences of finite shift-class groups. -/
def shiftClassEquiv {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) (q : ℕ) (hq : h ^ q = 1) :
    ShiftClassGroup G h q hq ≃+
      ShiftClassGroup H (e.pointGroupEquiv h) q (transportedPointPowerProof e h q hq) :=
  QuotientAddGroup.congr
    (normTranslationSubgroup G h q hq)
    (normTranslationSubgroup H (e.pointGroupEquiv h) q
      (transportedPointPowerProof e h q hq))
    (fixedTranslationEquiv e h)
    (normTranslationSubgroup_map e h q hq)

/-- The image of a lift is a lift of the image point element. -/
theorem mappedLiftProjection {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) (g : G.carrier)
    (hg : pointProjection G.carrier g = h) :
    pointProjection H.carrier (e.toMulEquiv g) = e.pointGroupEquiv h := by
  rw [← e.pointGroupEquiv_pointProjection, hg]

/-- Lift-power translation vectors are natural under translation-preserving isomorphisms. -/
theorem liftPowerTranslation_natural {G H : PlaneGroup}
    (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) (g : G.carrier) (hg : pointProjection G.carrier g = h) :
    e.translationVectorEquiv (liftPowerTranslation G h q hq g hg) =
      liftPowerTranslation H (e.pointGroupEquiv h) q
        (transportedPointPowerProof e h q hq) (e.toMulEquiv g)
        (mappedLiftProjection e h g hg) := by
  apply Subtype.ext
  apply translation_injective
  have hgq : (pointProjection G.carrier g) ^ q = 1 := by simpa [hg] using hq
  have htargetq : (pointProjection H.carrier (e.toMulEquiv g)) ^ q = 1 := by
    simpa [mappedLiftProjection e h g hg] using transportedPointPowerProof e h q hq
  calc
    translation
        (e.translationVectorEquiv (liftPowerTranslation G h q hq g hg) : Plane) =
        ((e.toMulEquiv
          (translationElement G.carrier (liftPowerTranslation G h q hq g hg)) :
            H.carrier) : EuclideanMotion Plane) :=
      (e.map_pureTranslation (liftPowerTranslation G h q hq g hg)).symm
    _ = ((e.toMulEquiv (g ^ q) : H.carrier) : EuclideanMotion Plane) := by
      apply congrArg (fun x : H.carrier => (x : EuclideanMotion Plane))
      apply congrArg e.toMulEquiv
      apply Subtype.ext
      exact (lift_pow_eq_translation G.carrier g q hgq).symm
    _ = (((e.toMulEquiv g) ^ q : H.carrier) : EuclideanMotion Plane) := by rw [map_pow]
    _ = translation
        (liftPowerTranslation H (e.pointGroupEquiv h) q
          (transportedPointPowerProof e h q hq) (e.toMulEquiv g)
          (mappedLiftProjection e h g hg) : Plane) :=
      lift_pow_eq_translation H.carrier (e.toMulEquiv g) q htargetq

/-- The fixed lift-power translation is natural under the induced fixed-subgroup equivalence. -/
theorem liftPowerFixedTranslation_natural {G H : PlaneGroup}
    (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) (g : G.carrier) (hg : pointProjection G.carrier g = h) :
    fixedTranslationEquiv e h (liftPowerFixedTranslation G h q hq g hg) =
      liftPowerFixedTranslation H (e.pointGroupEquiv h) q
        (transportedPointPowerProof e h q hq) (e.toMulEquiv g)
        (mappedLiftProjection e h g hg) := by
  apply Subtype.ext
  exact liftPowerTranslation_natural e h q hq g hg

/-- Shift classes are functorial under translation-preserving isomorphisms. -/
theorem shiftClass_natural {G H : PlaneGroup}
    (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) (q : ℕ)
    (hq : h ^ q = 1) (g : G.carrier) (hg : pointProjection G.carrier g = h) :
    shiftClassEquiv e h q hq (shiftClass G h q hq g hg) =
      shiftClass H (e.pointGroupEquiv h) q (transportedPointPowerProof e h q hq)
        (e.toMulEquiv g) (mappedLiftProjection e h g hg) := by
  change QuotientAddGroup.mk'
      (normTranslationSubgroup H (e.pointGroupEquiv h) q
        (transportedPointPowerProof e h q hq))
      (fixedTranslationEquiv e h (liftPowerFixedTranslation G h q hq g hg)) = _
  rw [liftPowerFixedTranslation_natural]
  rfl

/-- A shift class vanishes exactly when its lift-power translation lies in the norm image. -/
theorem shiftClass_eq_zero_iff
    (G : PlaneGroup) (h : pointGroup G.carrier) (q : ℕ) (hq : h ^ q = 1)
    (g : G.carrier) (hg : pointProjection G.carrier g = h) :
    shiftClass G h q hq g hg = 0 ↔
      liftPowerFixedTranslation G h q hq g hg ∈ normTranslationSubgroup G h q hq := by
  exact QuotientAddGroup.eq_zero_iff _

/-- Vanishing of the shift class is preserved and reflected by translation-preserving
isomorphisms. -/
theorem shiftClass_eq_zero_iff_map
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) (q : ℕ) (hq : h ^ q = 1)
    (g : G.carrier) (hg : pointProjection G.carrier g = h) :
    shiftClass G h q hq g hg = 0 ↔
      shiftClass H (e.pointGroupEquiv h) q (transportedPointPowerProof e h q hq)
        (e.toMulEquiv g) (mappedLiftProjection e h g hg) = 0 := by
  constructor
  · intro hs
    rw [← shiftClass_natural e h q hq g hg, hs, map_zero]
  · intro ht
    apply (shiftClassEquiv e h q hq).injective
    rw [shiftClass_natural e h q hq g hg, ht, map_zero]

end

end WallpaperGroups
