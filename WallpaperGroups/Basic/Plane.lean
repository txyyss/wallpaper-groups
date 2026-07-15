import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# The Euclidean plane

This module fixes the ambient plane used throughout the classification and records its canonical
coordinate basis and dimension.  The public type remains mathlib's Euclidean space, so its norm,
inner product, and finite-dimensional instances are available without adapters.
-/

set_option autoImplicit false

namespace WallpaperGroups

/-- The real Euclidean plane with coordinates indexed by `Fin 2`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Plane

/-- The Euclidean plane has real dimension two. -/
@[simp]
theorem finrank : Module.finrank ℝ Plane = 2 :=
  finrank_euclideanSpace_fin

/-- The canonical real coordinate basis of the Euclidean plane. -/
noncomputable def canonicalRealBasis : Module.Basis (Fin 2) ℝ Plane :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

/-- A vector of the canonical basis is the corresponding Euclidean coordinate vector. -/
@[simp]
theorem canonicalRealBasis_apply (i : Fin 2) :
    canonicalRealBasis i = EuclideanSpace.single i 1 := by
  simp [canonicalRealBasis, EuclideanSpace.basisFun_apply]

end Plane

end WallpaperGroups
