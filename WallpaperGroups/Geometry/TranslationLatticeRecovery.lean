import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.DiscreteSubset
import WallpaperGroups.Geometry.GeometricToStrong

set_option linter.style.header false

/-!
# Recovering the translation lattice of a geometric wallpaper group

This module implements the lattice-recovery stage of the converse geometric bridge.  Finiteness
of the point group transfers a compact orbit-representative set to the pure translations.
Proper discontinuity makes the resulting integer translation module discrete, while compact
translation representatives force its real span to be the whole plane.

The final construction uses `RankTwoLattice.ofZLattice`.  Its basis is noncanonical framing
data; the public carrier theorem records that the recovered lattice is exactly the original
translation module.  Constructing a strong `PlaneGroup` is deliberately deferred to M8c-c.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion
open Filter
open scoped RealInnerProductSpace Topology

noncomputable section

namespace MotionSubgroup

/-! ## Compact representatives for the translation subgroup -/

/--
A finite point group transfers compact orbit representatives from a motion subgroup to its
pure translations.

The proof chooses one lift of each point-group element only to construct a compact witness.
Neither the lifts nor that witness occur in the conclusion as classification data.
-/
theorem exists_compact_translation_representatives
    (Γ : Subgroup (EuclideanMotion Plane))
    [Finite (pointGroup Γ)]
    (hcoc : IsCocompact Γ) :
    ∃ K : Set Plane, IsCompact K ∧
      ∀ x : Plane,
        ∃ t : (translationVectors Γ).toIntSubmodule,
          (t : Plane) + x ∈ K := by
  classical
  rw [isCocompact_iff_exists_compact_orbit_representatives] at hcoc
  obtain ⟨K₀, hK₀, hrepresentatives⟩ := hcoc
  let lift : pointGroup Γ → Γ :=
    fun A => Classical.choose (pointProjection_surjective Γ A)
  have hlift (A : pointGroup Γ) :
      pointProjection Γ (lift A) = A :=
    Classical.choose_spec (pointProjection_surjective Γ A)
  let K : Set Plane :=
    ⋃ A : pointGroup Γ, (((lift A)⁻¹ : Γ) • ·) '' K₀
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro A
    exact hK₀.image
      (((lift A : Γ) : EuclideanMotion Plane)⁻¹).continuous
  refine ⟨K, hK, ?_⟩
  intro x
  obtain ⟨γ, hγx⟩ := hrepresentatives x
  let A : pointGroup Γ := pointProjection Γ γ
  let τ : Γ := (lift A)⁻¹ * γ
  have hτ : τ ∈ translationSubgroup Γ := by
    rw [← pointProjection_ker]
    change pointProjection Γ τ = 1
    simp [τ, A, hlift]
  obtain ⟨u, hu⟩ :=
    (mem_translationSubgroup_iff_exists Γ τ).mp hτ
  let t : (translationVectors Γ).toIntSubmodule :=
    ⟨(u : Plane), u.property⟩
  refine ⟨t, ?_⟩
  have hτx : τ • x = (t : Plane) + x := by
    change (τ : EuclideanMotion Plane) x = (t : Plane) + x
    rw [hu, translation_apply]
  rw [← hτx]
  exact Set.mem_iUnion_of_mem A ⟨γ • x, hγx, rfl⟩

/-! ## Discreteness of the translation module -/

/--
The integer module of translation vectors in a geometrically discrete motion subgroup has the
discrete induced topology.

For each compact `K`, proper discontinuity makes finite the motions carrying `{0}` into `K`.
The pure-translation embedding is injective, so the inclusion of the translation module into
the plane has finite preimage on every compact set.  The cofinite--cocompact criterion then
gives discreteness.
-/
theorem translationModule_discreteTopology
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : IsDiscrete Γ) :
    DiscreteTopology (translationVectors Γ).toIntSubmodule := by
  let L : Submodule ℤ Plane := (translationVectors Γ).toIntSubmodule
  let toΓ : L → Γ := fun t =>
    translationElement Γ
      ⟨(t : Plane), t.property⟩
  have htoΓ_injective : Function.Injective toΓ := by
    intro t u htu
    apply Subtype.ext
    apply translation_injective
    simpa only [toΓ, translationElement_coe] using
      congrArg (fun g : Γ => (g : EuclideanMotion Plane)) htu
  apply continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
  rw [tendsto_cofinite_cocompact_iff]
  intro K hK
  let F : Set Γ :=
    {γ | ((γ • ·) '' ({0} : Set Plane) ∩ K).Nonempty}
  have hF : F.Finite :=
    compact_intersections_finite Γ hdisc isCompact_singleton hK
  apply (hF.preimage htoΓ_injective.injOn).subset
  intro t ht
  change toΓ t ∈ F
  refine ⟨(t : Plane), ?_, ht⟩
  refine ⟨0, Set.mem_singleton 0, ?_⟩
  change translation (t : Plane) 0 = (t : Plane)
  rw [translation_apply, add_zero]

/-! ## Full real span -/

/--
A compact set meeting every orbit of an integer translation module forces that module to span
the whole plane over `ℝ`.

If the real span were proper, its orthogonal complement would contain a unit vector `v`.
Translation by the module cannot change the component along `v`; applying the representative
property to increasingly distant points on that line contradicts boundedness of the compact
set.
-/
theorem span_eq_top_of_compact_translation_representatives
    (L : Submodule ℤ Plane) (K : Set Plane)
    (hK : IsCompact K)
    (hrepresentatives : ∀ x : Plane, ∃ t : L, (t : Plane) + x ∈ K) :
    Submodule.span ℝ (L : Set Plane) = ⊤ := by
  classical
  let W : Submodule ℝ Plane := Submodule.span ℝ (L : Set Plane)
  by_contra hW
  have horth : Wᗮ ≠ ⊥ := by
    intro hbot
    apply hW
    exact Submodule.orthogonal_eq_bot_iff.mp hbot
  obtain ⟨u, huorth, hune⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot horth
  let v : Plane := NormedSpace.normalize u
  have hvorth : v ∈ Wᗮ :=
    (Submodule.orthogonal W).smul_mem (‖u‖⁻¹) huorth
  have hvnorm : ‖v‖ = 1 :=
    NormedSpace.norm_normalize hune
  obtain ⟨R, hRpos, hR⟩ :=
    hK.isBounded.exists_pos_norm_le
  let x : Plane := (R + 1) • v
  obtain ⟨t, htK⟩ := hrepresentatives x
  let tv : Plane := t
  let y : Plane := tv + x
  have htW : tv ∈ W :=
    Submodule.subset_span t.property
  have hvt : inner ℝ v tv = 0 :=
    Submodule.inner_left_of_mem_orthogonal htW hvorth
  have hynorm : ‖y‖ ≤ R :=
    hR y htK
  have hinner : inner ℝ v y = R + 1 := by
    rw [show y = tv + (R + 1) • v by rfl]
    rw [inner_add_right, hvt, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hvnorm]
    norm_num
  have hbound :=
    abs_real_inner_le_norm v y
  rw [hinner, hvnorm, one_mul,
    abs_of_pos (by positivity : 0 < R + 1)] at hbound
  linarith

/--
The integer module of translations in a cocompact motion subgroup with finite point group spans
the whole plane over `ℝ`.
-/
theorem translationModule_span_eq_top
    (Γ : Subgroup (EuclideanMotion Plane))
    [Finite (pointGroup Γ)]
    (hcoc : IsCocompact Γ) :
    Submodule.span ℝ
      ((translationVectors Γ).toIntSubmodule : Set Plane) = ⊤ := by
  obtain ⟨K, hK, hrepresentatives⟩ :=
    exists_compact_translation_representatives Γ hcoc
  exact span_eq_top_of_compact_translation_representatives
    (translationVectors Γ).toIntSubmodule K hK hrepresentatives

/-! ## Rank-two lattice packaging -/

/--
Recover the full rank-two translation lattice of a discrete cocompact plane-motion subgroup.

The chosen basis inside the result is noncanonical; `recoveredTranslationLattice_carrier` is
the stable, choice-independent description of the recovered object.
-/
def recoveredTranslationLattice
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : IsDiscrete Γ) (hcoc : IsCocompact Γ) :
    RankTwoLattice Plane := by
  let _ : Finite (pointGroup Γ) :=
    pointGroup_finite Γ hdisc hcoc
  let _ : DiscreteTopology (translationVectors Γ).toIntSubmodule :=
    translationModule_discreteTopology Γ hdisc
  let _ : IsZLattice ℝ (translationVectors Γ).toIntSubmodule :=
    ⟨translationModule_span_eq_top Γ hcoc⟩
  exact RankTwoLattice.ofZLattice
    (translationVectors Γ).toIntSubmodule

/-- The recovered lattice is exactly the actual integer module of translation vectors. -/
@[simp]
theorem recoveredTranslationLattice_carrier
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : IsDiscrete Γ) (hcoc : IsCocompact Γ) :
    (recoveredTranslationLattice Γ hdisc hcoc).carrier =
      (translationVectors Γ).toIntSubmodule := by
  simp [recoveredTranslationLattice]

end MotionSubgroup

namespace GeometricWallpaperGroup

/-- The translation module of a geometric wallpaper group has the discrete induced topology. -/
theorem translationModule_discreteTopology (X : GeometricWallpaperGroup) :
    DiscreteTopology (translationVectors X.carrier).toIntSubmodule :=
  MotionSubgroup.translationModule_discreteTopology X.carrier X.isDiscrete

/-- The translation module of a geometric wallpaper group spans the entire real plane. -/
theorem translationModule_span_eq_top (X : GeometricWallpaperGroup) :
    Submodule.span ℝ
      ((translationVectors X.carrier).toIntSubmodule : Set Plane) = ⊤ :=
  MotionSubgroup.translationModule_span_eq_top X.carrier X.isCocompact

/--
The recovered rank-two translation lattice of a geometric wallpaper group.

Its stored basis is construction data only; use `translationLattice_carrier` for stable
statements.
-/
def translationLattice (X : GeometricWallpaperGroup) :
    RankTwoLattice Plane :=
  MotionSubgroup.recoveredTranslationLattice
    X.carrier X.isDiscrete X.isCocompact

/-- The bundled recovered lattice has exactly the original translation-module carrier. -/
@[simp]
theorem translationLattice_carrier (X : GeometricWallpaperGroup) :
    X.translationLattice.carrier =
      (translationVectors X.carrier).toIntSubmodule :=
  MotionSubgroup.recoveredTranslationLattice_carrier
    X.carrier X.isDiscrete X.isCocompact

end GeometricWallpaperGroup

end

end WallpaperGroups
