import Mathlib.Algebra.Group.Subgroup.Finite
import WallpaperGroups.Basic.RankTwoLattice
import WallpaperGroups.Invariants.ExactSequence

set_option linter.style.header false

/-!
# Plane groups

This module packages the strong definition used in the classification: the pure translations
are exactly a rank-two lattice and the point group is finite.  No discreteness, cocompactness,
orientation, metric normal form, or choice of classification label is stored here.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/--
A plane group is a subgroup of Euclidean motions whose full pure-translation subgroup is a
rank-two lattice and whose point group is finite.

The selected lattice basis is computational framing data.  The equality field identifies the
entire translation carrier, so it cannot omit translations or retain only a finite-index
sublattice.
-/
structure PlaneGroup where
  carrier : Subgroup (EuclideanMotion Plane)
  translationLattice : RankTwoLattice Plane
  translationLattice_carrier :
    translationLattice.carrier = (translationVectors carrier).toIntSubmodule
  pointGroup_finite : Finite (pointGroup carrier)

namespace PlaneGroup

/-- The motion subgroup underlying a plane group. -/
abbrev motionGroup (G : PlaneGroup) : Subgroup (EuclideanMotion Plane) :=
  G.carrier

/-- The finite point-group instance stored by the strong plane-group definition. -/
instance pointGroupFinite (G : PlaneGroup) : Finite (pointGroup G.carrier) :=
  G.pointGroup_finite

/-- The stored lattice carrier is exactly the integer submodule of all translation vectors. -/
theorem translationLattice_carrier_eq (G : PlaneGroup) :
    G.translationLattice.carrier = (translationVectors G.carrier).toIntSubmodule :=
  G.translationLattice_carrier

/-- Additively, the stored lattice carrier is exactly the full group of translation vectors. -/
theorem translationLattice_toAddSubgroup_eq (G : PlaneGroup) :
    G.translationLattice.carrier.toAddSubgroup = translationVectors G.carrier := by
  rw [G.translationLattice_carrier]
  exact AddSubgroup.toIntSubmodule_toAddSubgroup _

/-- A stored lattice element, viewed as the corresponding translation vector. -/
def latticeTranslationEquiv (G : PlaneGroup) :
    G.translationLattice.carrier ≃+ translationVectors G.carrier :=
  AddEquiv.addSubgroupCongr G.translationLattice_toAddSubgroup_eq

/-- The lattice-to-translation equivalence does not change the underlying plane vector. -/
@[simp]
theorem latticeTranslationEquiv_coe (G : PlaneGroup)
    (t : G.translationLattice.carrier) :
    (G.latticeTranslationEquiv t : Plane) = (t : Plane) :=
  rfl

/-- The inverse translation-to-lattice equivalence does not change the underlying plane vector. -/
@[simp]
theorem latticeTranslationEquiv_symm_coe (G : PlaneGroup)
    (t : translationVectors G.carrier) :
    (G.latticeTranslationEquiv.symm t : Plane) = (t : Plane) :=
  rfl

/-- Membership in the stored lattice is membership among the actual translation vectors. -/
@[simp]
theorem mem_translationLattice_iff (G : PlaneGroup) (t : Plane) :
    t ∈ G.translationLattice.carrier ↔ t ∈ translationVectors G.carrier := by
  rw [G.translationLattice_carrier]
  rfl

/-- A plane vector is in the stored lattice exactly when its pure translation lies in the group. -/
theorem mem_translationLattice_iff_translation_mem (G : PlaneGroup) (t : Plane) :
    t ∈ G.translationLattice.carrier ↔ translation t ∈ G.carrier := by
  rw [G.mem_translationLattice_iff]
  exact mem_translationVectors

/-- The chosen two-element integer basis of the translation lattice. -/
abbrev chosenBasis (G : PlaneGroup) :
    Module.Basis (Fin 2) ℤ G.translationLattice.carrier :=
  G.translationLattice.basis

/-- The chosen lattice basis, promoted to a real basis of the whole Euclidean plane. -/
abbrev realBasis (G : PlaneGroup) : Module.Basis (Fin 2) ℝ Plane :=
  G.translationLattice.realBasis

/-- The real span of all translation vectors of a plane group is the entire plane. -/
theorem translation_real_span_eq_top (G : PlaneGroup) :
    Submodule.span ℝ (translationVectors G.carrier : Set Plane) = ⊤ := by
  rw [← G.translationLattice_toAddSubgroup_eq]
  simpa using G.translationLattice.real_span_eq_top

/--
Replace only the chosen computational lattice frame, leaving the motion subgroup, full
translation carrier, and finite point group unchanged.
-/
def reframe (G : PlaneGroup)
    (basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (basis_real_linearIndependent :
      LinearIndependent ℝ (fun i => (basis i : Plane))) : PlaneGroup where
  carrier := G.carrier
  translationLattice := G.translationLattice.reframe basis basis_real_linearIndependent
  translationLattice_carrier := G.translationLattice_carrier
  pointGroup_finite := G.pointGroup_finite

/-- Reframing does not change the underlying motion subgroup. -/
@[simp]
theorem reframe_carrier (G : PlaneGroup)
    (basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (hbasis : LinearIndependent ℝ (fun i => (basis i : Plane))) :
    (G.reframe basis hbasis).carrier = G.carrier :=
  rfl

/-- Reframing does not change the lattice carrier. -/
@[simp]
theorem reframe_translationLattice_carrier (G : PlaneGroup)
    (basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (hbasis : LinearIndependent ℝ (fun i => (basis i : Plane))) :
    (G.reframe basis hbasis).translationLattice.carrier =
      G.translationLattice.carrier :=
  rfl

end PlaneGroup

end

end WallpaperGroups
