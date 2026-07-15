import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

set_option linter.style.header false

/-!
# M0 mathlib API audit

This file keeps representative `#check` experiments and three small proofs from the M0 audit in
the build.  The focused representation experiments are in `EuclideanMotion.lean` and
`RankTwoLattice.lean`; none of these declarations is the stable M1 API.
-/

set_option autoImplicit false

namespace WallpaperGroups.Prototype.APIAudit

#check AffineIsometryEquiv.linearIsometryEquiv
#check LinearIsometryEquiv.toLinearEquiv
#check Matrix.orthogonalGroup
#check Matrix.specialOrthogonalGroup
#check SemidirectProduct.inl_aut
#check AddSubgroup.toIntSubmodule
#check IsZLattice
#check Module.Basis.equivFun
#check Module.Basis.restrictScalars
#check ZMod
#check zmodCyclicMulEquiv
#check DihedralGroup
#check GroupExtension
#check Matrix.trace
#check Matrix.det
#check Matrix.charpoly_fin_two
#check Matrix.aeval_self_charpoly
#check QuotientAddGroup.eq_iff_sub_mem
#check Submodule.Quotient.equiv
#check Orientation.rotation
#check Submodule.reflection

/-- A finite group has finite subgroups in the typeclass-based API used by the roadmap. -/
example {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Finite H := by
  infer_instance

/-- Finiteness of a homomorphism range is transported explicitly from its domain. -/
example {G K : Type*} [Group G] [Group K] [Finite G] (f : G →* K) : Finite f.range :=
  Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective

/-- Every homomorphism gives the kernel--range group extension needed for the point group. -/
def kernelRangeExtension {E G : Type*} [Group E] [Group G] (f : E →* G) :
    GroupExtension f.ker E f.range where
  inl := f.ker.subtype
  rightHom := f.rangeRestrict
  inl_injective := f.ker.subtype_injective
  range_inl_eq_ker_rightHom := by
    ext e
    simp
  rightHom_surjective := f.rangeRestrict_surjective

/-- The exact integral `2 × 2` Cayley--Hamilton identity intended for the M3 route. -/
example (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A ^ 2 - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) = 0 := by
  have h := Matrix.aeval_self_charpoly A
  rw [Matrix.charpoly_fin_two] at h
  simpa [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.smul_def, smul_eq_mul] using h

end WallpaperGroups.Prototype.APIAudit
