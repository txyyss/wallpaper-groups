import WallpaperGroups.Classification.OneReflection

set_option linter.style.header false

/-!
# Reflection-family invariants

This file proves that translation-preserving equivalence preserves orientation in the point
group.  It packages the induced equivalence of orientation-preserving subgroups and gives the
mutually exclusive no-, one-, and multiple-reflection trichotomy used by the global classifier.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

namespace TranslationPreservingIso

variable {G H : PlaneGroup}

/-- Conjugate integral lattice actions have equal determinant. -/
theorem latticeActionMatrix_det (e : TranslationPreservingIso G H)
    (h : pointGroup G.carrier) :
    (H.latticeActionMatrix (e.pointGroupEquiv h)).det =
      (G.latticeActionMatrix h).det := by
  have hc := e.integralRepresentation_conjugacy h
  have hd : Matrix.GeneralLinearGroup.det
        (H.integralRepresentation (e.pointGroupEquiv h)) =
      Matrix.GeneralLinearGroup.det (G.integralRepresentation h) := by
    rw [hc, map_mul, map_mul, map_inv]
    simp [mul_comm, mul_left_comm]
  have hdv := congrArg Units.val hd
  change (H.translationLattice.equivMatrix H.translationLattice
      (H.latticeAction (e.pointGroupEquiv h))).det =
    (G.translationLattice.equivMatrix G.translationLattice
      (G.latticeAction h)).det
  exact hdv

/-- The induced point-group equivalence preserves and reflects positive determinant. -/
theorem pointGroupEquiv_mem_orientationPreserving_iff
    (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) :
    e.pointGroupEquiv h ∈ orientationPreservingPointGroup H ↔
      h ∈ orientationPreservingPointGroup G := by
  have hd : LinearMap.det
        ((e.pointGroupEquiv h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) =
      LinearMap.det ((h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane) := by
    rw [← H.det_cast, ← G.det_cast]
    exact_mod_cast e.latticeActionMatrix_det h
  constructor
  · intro hp
    change 0 < ((pointGroupDet H (e.pointGroupEquiv h) : ℝˣ) : ℝ) at hp
    change 0 < ((pointGroupDet G h : ℝˣ) : ℝ)
    simpa only [pointGroupDet_apply, hd] using hp
  · intro hp
    change 0 < ((pointGroupDet G h : ℝˣ) : ℝ) at hp
    change 0 < ((pointGroupDet H (e.pointGroupEquiv h) : ℝˣ) : ℝ)
    simpa only [pointGroupDet_apply, hd] using hp

/-- The canonical equivalence between the two positive point subgroups. -/
noncomputable def orientationPreservingPointGroupEquiv
    (e : TranslationPreservingIso G H) :
    orientationPreservingPointGroup G ≃* orientationPreservingPointGroup H :=
  (e.pointGroupEquiv.subgroupMap (orientationPreservingPointGroup G)).trans
    (MulEquiv.subgroupCongr (by
      ext h
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact (e.pointGroupEquiv_mem_orientationPreserving_iff g).2 hg
      · intro hh
        refine ⟨e.pointGroupEquiv.symm h, ?_, by simp⟩
        apply (e.pointGroupEquiv_mem_orientationPreserving_iff
          (e.pointGroupEquiv.symm h)).1
        simpa))

/-- Conjugation by an element of a plane group is a translation-preserving automorphism. -/
def inner (G : PlaneGroup) (g : G.carrier) : TranslationPreservingIso G G where
  toMulEquiv := MulAut.conj g
  map_translationSubgroup := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (translationSubgroup_normal G.carrier).conj_mem x hx g
    · intro hy
      refine ⟨(MulAut.conj g).symm y, ?_, (MulAut.conj g).apply_symm_apply y⟩
      exact (translationSubgroup_normal G.carrier).conj_mem' y hy g

/-- The induced point automorphism of an inner plane-group automorphism is point-group
conjugation. -/
@[simp]
theorem inner_pointGroupEquiv
    (G : PlaneGroup) (g : G.carrier) (h : pointGroup G.carrier) :
    (inner G g).pointGroupEquiv h =
      pointProjection G.carrier g * h * (pointProjection G.carrier g)⁻¹ := by
  obtain ⟨x, rfl⟩ := pointProjection_surjective G.carrier h
  rw [pointGroupEquiv_pointProjection]
  change pointProjection G.carrier ((MulAut.conj g) x) = _
  simp

end TranslationPreservingIso

/-- A point group has multiple reflections precisely in the remaining dihedral case: a
reversing element exists and the positive subgroup is nontrivial. -/
def PointGroupHasMultipleReflections (G : PlaneGroup) : Prop :=
  (∃ s : pointGroup G.carrier, s ∉ orientationPreservingPointGroup G) ∧
    ∃ r : orientationPreservingPointGroup G, r ≠ 1

/-- Every plane point group lies in exactly one of the three reflection families. -/
theorem pointGroup_reflection_trichotomy (G : PlaneGroup) :
    PointGroupHasNoReflections G ∨ PointGroupHasOneReflection G ∨
      PointGroupHasMultipleReflections G := by
  by_cases hall : ∀ s : pointGroup G.carrier,
      s ∈ orientationPreservingPointGroup G
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨s, hs⟩ := hall
    by_cases htriv : ∀ r : orientationPreservingPointGroup G, r = 1
    · exact Or.inl ⟨s, hs, htriv⟩
    · push Not at htriv
      exact Or.inr ⟨⟨s, hs⟩, htriv⟩

theorem pointGroupHasNoReflections_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (hG : PointGroupHasNoReflections G) : PointGroupHasNoReflections H := by
  intro h
  let g := e.pointGroupEquiv.symm h
  have hg := hG g
  have hm := (e.pointGroupEquiv_mem_orientationPreserving_iff g).2 hg
  simpa [g] using hm

theorem pointGroupHasNoReflections_iff_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H) :
    PointGroupHasNoReflections G ↔ PointGroupHasNoReflections H :=
  ⟨pointGroupHasNoReflections_of_iso e, pointGroupHasNoReflections_of_iso e.symm⟩

theorem pointGroupHasOneReflection_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (hG : PointGroupHasOneReflection G) : PointGroupHasOneReflection H := by
  obtain ⟨s, hs, htriv⟩ := hG
  refine ⟨e.pointGroupEquiv s, ?_, ?_⟩
  · intro hm
    exact hs ((e.pointGroupEquiv_mem_orientationPreserving_iff s).1 hm)
  · intro r
    let eO := e.orientationPreservingPointGroupEquiv
    have hr := congrArg eO (htriv (eO.symm r))
    simpa [eO] using hr

theorem pointGroupHasOneReflection_iff_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H) :
    PointGroupHasOneReflection G ↔ PointGroupHasOneReflection H :=
  ⟨pointGroupHasOneReflection_of_iso e, pointGroupHasOneReflection_of_iso e.symm⟩

theorem pointGroupHasMultipleReflections_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (hG : PointGroupHasMultipleReflections G) :
    PointGroupHasMultipleReflections H := by
  obtain ⟨⟨s, hs⟩, ⟨r, hr⟩⟩ := hG
  refine ⟨⟨e.pointGroupEquiv s, ?_⟩, ?_⟩
  · intro hm
    exact hs ((e.pointGroupEquiv_mem_orientationPreserving_iff s).1 hm)
  · let eO := e.orientationPreservingPointGroupEquiv
    refine ⟨eO r, ?_⟩
    intro heq
    apply hr
    apply eO.injective
    simpa [eO] using heq

theorem pointGroupHasMultipleReflections_iff_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H) :
    PointGroupHasMultipleReflections G ↔ PointGroupHasMultipleReflections H :=
  ⟨pointGroupHasMultipleReflections_of_iso e,
    pointGroupHasMultipleReflections_of_iso e.symm⟩

/-- The no- and one-reflection families are disjoint. -/
theorem noReflections_not_oneReflection (G : PlaneGroup) :
    ¬ (PointGroupHasNoReflections G ∧ PointGroupHasOneReflection G) := by
  rintro ⟨hno, ⟨s, hs, -⟩⟩
  exact hs (hno s)

/-- The no- and multiple-reflection families are disjoint. -/
theorem noReflections_not_multipleReflections (G : PlaneGroup) :
    ¬ (PointGroupHasNoReflections G ∧ PointGroupHasMultipleReflections G) := by
  rintro ⟨hno, ⟨⟨s, hs⟩, -⟩⟩
  exact hs (hno s)

/-- The one- and multiple-reflection families are disjoint. -/
theorem oneReflection_not_multipleReflections (G : PlaneGroup) :
    ¬ (PointGroupHasOneReflection G ∧ PointGroupHasMultipleReflections G) := by
  rintro ⟨⟨-, -, htriv⟩, ⟨-, ⟨r, hr⟩⟩⟩
  exact hr (htriv r)

end

end WallpaperGroups
