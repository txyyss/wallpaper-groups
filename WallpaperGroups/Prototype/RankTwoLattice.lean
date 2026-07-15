import WallpaperGroups.Invariants.EquivalenceAction

set_option linter.style.header false

/-!
# Rank-two-lattice and M2 regression tests

The M0 candidate has been migrated to the production `RankTwoLattice` API.  This file now checks
the standard lattice, coordinates, real basis, integral action, translation-preserving
equivalence, and matrix-conjugacy interfaces.  Production modules never import this file.
-/

set_option autoImplicit false

namespace WallpaperGroups.Prototype

open WallpaperGroups.EuclideanMotion

noncomputable section

/-- The production standard copy of `ℤ²` inside the Euclidean plane. -/
abbrev standardRankTwoLattice : RankTwoLattice Plane :=
  RankTwoLattice.standardLattice

example (z : Fin 2 → ℤ) :
    standardRankTwoLattice.coordinates (standardRankTwoLattice.ofCoordinates z) = z := by
  simp

example (x : standardRankTwoLattice.carrier) :
    standardRankTwoLattice.ofCoordinates (standardRankTwoLattice.coordinates x) = x := by
  simp

example :
    LinearIndependent ℝ (fun i => (standardRankTwoLattice.basis i : Plane)) :=
  standardRankTwoLattice.basis_real_linearIndependent

example (i : Fin 2) :
    standardRankTwoLattice.realBasis i = (standardRankTwoLattice.basis i : Plane) := by
  simp

example : Submodule.span ℝ (standardRankTwoLattice.carrier : Set Plane) = ⊤ :=
  standardRankTwoLattice.real_span_eq_top

example (f : standardRankTwoLattice.carrier ≃ₗ[ℤ] standardRankTwoLattice.carrier) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  standardRankTwoLattice.equivMatrix standardRankTwoLattice f

example (f : standardRankTwoLattice.carrier ≃ₗ[ℤ] standardRankTwoLattice.carrier) :
    Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  standardRankTwoLattice.equivGL standardRankTwoLattice f

example :
    standardRankTwoLattice.equivMatrix standardRankTwoLattice
      (LinearEquiv.refl ℤ standardRankTwoLattice.carrier) = 1 := by
  simp

example {L L' L'' : RankTwoLattice Plane}
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) (g : L'.carrier ≃ₗ[ℤ] L''.carrier) :
    L.equivMatrix L'' (f.trans g) = L'.equivMatrix L'' g * L.equivMatrix L' f :=
  L.equivMatrix_trans L' L'' f g

example {L L' : RankTwoLattice Plane} (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    L'.equivMatrix L f.symm =
      (↑((L.equivGL L' f)⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) := by
  simp

example {L : RankTwoLattice Plane}
    (basis : Module.Basis (Fin 2) ℤ L.carrier)
    (hbasis : LinearIndependent ℝ (fun i => (basis i : Plane)))
    (a : L.carrier ≃ₗ[ℤ] L.carrier) :
    (L.reframe basis hbasis).equivMatrix (L.reframe basis hbasis) a =
      L.basisChangeMatrix basis hbasis * L.equivMatrix L a *
        (L.reframe basis hbasis).equivMatrix L (LinearEquiv.refl ℤ L.carrier) :=
  L.matrix_conjugacy_reframe basis hbasis a

/-- The strong constructor accepts exactly a motion group, its full rank-two translations, and
finite point-group evidence. -/
example (carrier : Subgroup (EuclideanMotion Plane)) (L : RankTwoLattice Plane)
    (hcarrier : L.carrier = (translationVectors carrier).toIntSubmodule)
    (hfinite : Finite (pointGroup carrier)) : PlaneGroup where
  carrier := carrier
  translationLattice := L
  translationLattice_carrier := hcarrier
  pointGroup_finite := hfinite

variable (G H K : PlaneGroup)

example : Finite (pointGroup G.carrier) := inferInstance

example (h : pointGroup G.carrier) :
    G.translationLattice.carrier ≃ₗ[ℤ] G.translationLattice.carrier :=
  G.latticeAction h

example : Function.Injective G.latticeActionHom :=
  G.latticeActionHom_injective

example : Function.Injective G.integralRepresentation :=
  G.integralRepresentation_injective

example : TranslationPreservingIso G G :=
  TranslationPreservingIso.refl G

example (e : TranslationPreservingIso G H) : TranslationPreservingIso H G :=
  e.symm

example (e : TranslationPreservingIso G H) (f : TranslationPreservingIso H K) :
    TranslationPreservingIso G K :=
  e.trans f

example (e : TranslationPreservingIso G H) :
    translationSubgroup G.carrier ≃* translationSubgroup H.carrier :=
  e.translationSubgroupEquiv

example (e : TranslationPreservingIso G H) :
    G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier :=
  e.translationLatticeEquiv

example (e : TranslationPreservingIso G H) :
    pointGroup G.carrier ≃* pointGroup H.carrier :=
  e.pointGroupEquiv

example (e : TranslationPreservingIso G H) (g : G.carrier) :
    e.pointGroupEquiv (pointProjection G.carrier g) =
      pointProjection H.carrier (e.toMulEquiv g) := by
  simp

example (e : TranslationPreservingIso G H) (h : pointGroup G.carrier)
    (t : translationVectors G.carrier) :
    e.translationVectorEquiv (pointAction G.carrier h t) =
      pointAction H.carrier (e.pointGroupEquiv h) (e.translationVectorEquiv t) :=
  e.translationVector_pointAction h t

example (e : TranslationPreservingIso G H) (h : pointGroup G.carrier)
    (t : G.translationLattice.carrier) :
    e.translationLatticeEquiv (G.latticeAction h t) =
      H.latticeAction (e.pointGroupEquiv h) (e.translationLatticeEquiv t) :=
  e.translationLattice_pointAction h t

example (e : TranslationPreservingIso G H) : Plane ≃ₗ[ℝ] Plane :=
  e.realLinearEquiv

example (e : TranslationPreservingIso G H) (t : G.translationLattice.carrier) :
    e.realLinearEquiv (t : Plane) = (e.translationLatticeEquiv t : Plane) := by
  simp

example (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) (x : Plane) :
    e.realLinearEquiv ((h : Plane ≃ₗᵢ[ℝ] Plane) x) =
      (e.pointGroupEquiv h : Plane ≃ₗᵢ[ℝ] Plane) (e.realLinearEquiv x) :=
  e.realLinearEquiv_pointAction h x

example (e : TranslationPreservingIso G H) (h : pointGroup G.carrier) :
    H.latticeActionMatrix (e.pointGroupEquiv h) =
      G.translationLattice.equivMatrix H.translationLattice e.translationLatticeEquiv *
        G.latticeActionMatrix h *
          H.translationLattice.equivMatrix G.translationLattice
            e.translationLatticeEquiv.symm :=
  e.integralMatrix_conjugacy h

example (basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (hbasis : LinearIndependent ℝ (fun i => (basis i : Plane))) :
    G.Equivalent (G.reframe basis hbasis) :=
  G.reframe_equivalent basis hbasis

end

end WallpaperGroups.Prototype
