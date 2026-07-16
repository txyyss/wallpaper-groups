import WallpaperGroups.Models.WallpaperModels

set_option linter.style.header false

/-!
# The seventeen-class wallpaper-group theorem

The reflection-family trichotomy combines the completed `5 + 3 + 9` component classifiers.
Family predicates are invariant under translation-preserving isomorphism and pairwise disjoint,
so the component-model inequivalence theorems also give global uniqueness.
-/

set_option autoImplicit false

namespace WallpaperGroups

noncomputable section

/-! ## Disjointness of the three standard-model families -/

/-- A standard rotation model cannot be equivalent to a standard one-reflection model. -/
theorem rotationModel_not_equivalent_oneReflectionModel
    (q : CrystallographicOrder) (w : OneReflectionType) :
    ¬ PlaneGroup.Equivalent (rotationModel q) w.model := by
  rintro ⟨e⟩
  apply noReflections_not_oneReflection w.model
  exact ⟨pointGroupHasNoReflections_of_iso e (rotationModel_hasNoReflections q),
    oneReflectionModel_hasOneReflection w⟩

/-- A standard rotation model cannot be equivalent to a multiple-reflection model. -/
theorem rotationModel_not_equivalent_multipleReflectionModel
    (q : CrystallographicOrder) (w : MultipleReflectionType) :
    ¬ PlaneGroup.Equivalent (rotationModel q) w.model := by
  rintro ⟨e⟩
  apply noReflections_not_multipleReflections w.model
  exact ⟨pointGroupHasNoReflections_of_iso e (rotationModel_hasNoReflections q),
    multipleReflectionModel_hasMultipleReflections w⟩

/-- A standard one-reflection model cannot be equivalent to a multiple-reflection model. -/
theorem oneReflectionModel_not_equivalent_multipleReflectionModel
    (w : OneReflectionType) (v : MultipleReflectionType) :
    ¬ PlaneGroup.Equivalent w.model v.model := by
  rintro ⟨e⟩
  apply oneReflection_not_multipleReflections v.model
  exact ⟨pointGroupHasOneReflection_of_iso e (oneReflectionModel_hasOneReflection w),
    multipleReflectionModel_hasMultipleReflections v⟩

/-! ## Pairwise inequivalence of all standard models -/

/-- Two component signatures have equivalent models exactly when the signatures agree. -/
theorem WallpaperSignature.models_equivalent_iff (s t : WallpaperSignature) :
    PlaneGroup.Equivalent s.model t.model ↔ s = t := by
  constructor
  · intro h
    cases s with
    | noReflections q =>
        cases t with
        | noReflections r =>
            exact congrArg WallpaperSignature.noReflections
              ((rotationModels_equivalent_iff q r).mp h)
        | oneReflection w =>
            exact (rotationModel_not_equivalent_oneReflectionModel q w h).elim
        | multipleReflections w =>
            exact (rotationModel_not_equivalent_multipleReflectionModel q w h).elim
    | oneReflection w =>
        cases t with
        | noReflections q =>
            exact (rotationModel_not_equivalent_oneReflectionModel q w
              (PlaneGroup.Equivalent.symm h)).elim
        | oneReflection v =>
            exact congrArg WallpaperSignature.oneReflection
              ((oneReflectionModels_equivalent_iff w v).mp h)
        | multipleReflections v =>
            exact (oneReflectionModel_not_equivalent_multipleReflectionModel w v h).elim
    | multipleReflections w =>
        cases t with
        | noReflections q =>
            exact (rotationModel_not_equivalent_multipleReflectionModel q w
              (PlaneGroup.Equivalent.symm h)).elim
        | oneReflection v =>
            exact (oneReflectionModel_not_equivalent_multipleReflectionModel v w
              (PlaneGroup.Equivalent.symm h)).elim
        | multipleReflections v =>
            exact congrArg WallpaperSignature.multipleReflections
              ((MultipleReflectionType.models_equivalent_iff w v).mp h)
  · rintro rfl
    exact PlaneGroup.Equivalent.refl _

/-- Two of the seventeen standard models are equivalent exactly when their labels agree. -/
theorem WallpaperType.models_equivalent_iff (w v : WallpaperType) :
    PlaneGroup.Equivalent w.model v.model ↔ w = v := by
  constructor
  · intro h
    have hs : w.signature = v.signature :=
      (WallpaperSignature.models_equivalent_iff w.signature v.signature).mp (by
        simpa only [WallpaperType.signature_model] using h)
    simpa only [WallpaperType.wallpaperType_signature] using
      congrArg WallpaperSignature.wallpaperType hs
  · rintro rfl
    exact PlaneGroup.Equivalent.refl _

/-- Distinct wallpaper labels give inequivalent standard plane groups. -/
theorem WallpaperType.not_equivalent_of_ne
    {w v : WallpaperType} (h : w ≠ v) :
    ¬ PlaneGroup.Equivalent w.model v.model := by
  intro he
  exact h ((w.models_equivalent_iff v).mp he)

/-! ## Global existence and unique classification -/

/-- Every plane group is equivalent to one of the seventeen standard models. -/
theorem exists_equivalent_wallpaperModel (G : PlaneGroup) :
    ∃ w : WallpaperType, PlaneGroup.Equivalent G w.model := by
  rcases pointGroup_reflection_trichotomy G with hno | hone | hmultiple
  · obtain ⟨q, hq, _⟩ := classify_no_reflections G hno
    cases q with
    | one => exact ⟨.p1, hq⟩
    | two => exact ⟨.p2, hq⟩
    | three => exact ⟨.p3, hq⟩
    | four => exact ⟨.p4, hq⟩
    | six => exact ⟨.p6, hq⟩
  · obtain ⟨w, hw, _⟩ := classify_one_reflection G hone
    cases w with
    | cm => exact ⟨.cm, hw⟩
    | pm => exact ⟨.pm, hw⟩
    | pg => exact ⟨.pg, hw⟩
  · obtain ⟨w, hw, _⟩ := classify_multiple_reflections G hmultiple
    cases w with
    | cmm => exact ⟨.cmm, hw⟩
    | pmm => exact ⟨.pmm, hw⟩
    | pmg => exact ⟨.pmg, hw⟩
    | pgg => exact ⟨.pgg, hw⟩
    | p3m1 => exact ⟨.p3m1, hw⟩
    | p31m => exact ⟨.p31m, hw⟩
    | p4m => exact ⟨.p4m, hw⟩
    | p4g => exact ⟨.p4g, hw⟩
    | p6m => exact ⟨.p6m, hw⟩

/-- Every plane group is equivalent to exactly one of the seventeen standard models. -/
theorem classification (G : PlaneGroup) :
    ∃! w : WallpaperType,
      PlaneGroup.Equivalent G (WallpaperType.model w) := by
  obtain ⟨w, hw⟩ := exists_equivalent_wallpaperModel G
  refine ⟨w, hw, ?_⟩
  intro v hv
  apply (WallpaperType.models_equivalent_iff v w).mp
  exact PlaneGroup.Equivalent.trans (PlaneGroup.Equivalent.symm hv) hw

end

end WallpaperGroups
