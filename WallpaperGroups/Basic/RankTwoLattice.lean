import WallpaperGroups.Basic.Plane
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option linter.style.header false

/-!
# Rank-two integer lattices

A rank-two lattice is stored as an integer submodule with a chosen two-element integer basis whose
vectors remain linearly independent over the reals.  This gives unique integral coordinates while
keeping the ambient embedding explicit.  The second half of the file develops the matrix,
`GL₂(ℤ)`, basis-change, and real-extension interfaces used by the classification.
-/

set_option autoImplicit false

namespace WallpaperGroups

noncomputable section

/-- An integer submodule with a chosen two-element basis that is real-linearly independent. -/
structure RankTwoLattice (E : Type*) [AddCommGroup E] [Module ℝ E] where
  carrier : Submodule ℤ E
  basis : Module.Basis (Fin 2) ℤ carrier
  basis_real_linearIndependent :
    LinearIndependent ℝ (fun i => (basis i : E))

namespace RankTwoLattice

variable {E E' E'' : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup E'] [Module ℝ E']
variable [AddCommGroup E''] [Module ℝ E'']

/-- Carrier and chosen basis determine a rank-two lattice; the independence proof is irrelevant. -/
@[ext]
theorem ext {L L' : RankTwoLattice E} (hcarrier : L.carrier = L'.carrier)
    (hbasis : HEq L.basis L'.basis) : L = L' := by
  cases L with
  | mk carrier basis hli =>
    cases L' with
    | mk carrier' basis' hli' =>
      dsimp at hcarrier hbasis
      subst carrier'
      cases hbasis
      rfl

/-- Regard a rank-two lattice as its integer submodule when a submodule is expected. -/
instance : Coe (RankTwoLattice E) (Submodule ℤ E) :=
  ⟨RankTwoLattice.carrier⟩

/-- Membership in a rank-two lattice means membership in its integer carrier. -/
instance : Membership E (RankTwoLattice E) :=
  ⟨fun L x => x ∈ L.carrier⟩

/-- The underlying additive subgroup of a rank-two lattice. -/
def toAddSubgroup (L : RankTwoLattice E) : AddSubgroup E :=
  L.carrier.toAddSubgroup

/-- Membership in the additive carrier is ordinary lattice membership. -/
@[simp]
theorem mem_toAddSubgroup (L : RankTwoLattice E) (x : E) :
    x ∈ L.toAddSubgroup ↔ x ∈ L.carrier :=
  Iff.rfl

/-- The additive carrier and integer-submodule carrier have the same underlying set. -/
@[simp]
theorem coe_toAddSubgroup (L : RankTwoLattice E) :
    (L.toAddSubgroup : Set E) = (L.carrier : Set E) :=
  rfl

/-- Two lattice elements are equal when their ambient vectors are equal. -/
@[ext]
theorem carrier_ext (L : RankTwoLattice E) {x y : L.carrier}
    (h : (x : E) = (y : E)) : x = y :=
  Subtype.ext h

/-- Equal carriers give a canonical integer-linear equivalence of their element types. -/
def carrierEquivOfEq (L L' : RankTwoLattice E) (h : L.carrier = L'.carrier) :
    L.carrier ≃ₗ[ℤ] L'.carrier :=
  LinearEquiv.ofEq L.carrier L'.carrier h

/-- Carrier transport does not change the ambient vector. -/
@[simp]
theorem carrierEquivOfEq_apply (L L' : RankTwoLattice E)
    (h : L.carrier = L'.carrier) (x : L.carrier) :
    (L.carrierEquivOfEq L' h x : E) = x :=
  rfl

/-- An additive equivalence of carriers is canonically integer-linear. -/
def equivOfAddEquiv (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.toAddSubgroup ≃+ L'.toAddSubgroup) : L.carrier ≃ₗ[ℤ] L'.carrier :=
  f.toIntLinearEquiv

/-- The integer-linear carrier equivalence has the same underlying function. -/
@[simp]
theorem equivOfAddEquiv_apply (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.toAddSubgroup ≃+ L'.toAddSubgroup) (x : L.carrier) :
    L.equivOfAddEquiv L' f x = f x :=
  rfl

/-- Unique integer coordinates in the chosen lattice basis. -/
def coordinates (L : RankTwoLattice E) : L.carrier ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  L.basis.equivFun

/-- Reconstruct a lattice element from its two integer coordinates. -/
def ofCoordinates (L : RankTwoLattice E) : (Fin 2 → ℤ) ≃ₗ[ℤ] L.carrier :=
  L.coordinates.symm

/-- Coordinate reconstruction is a left inverse. -/
@[simp]
theorem coordinates_ofCoordinates (L : RankTwoLattice E) (z : Fin 2 → ℤ) :
    L.coordinates (L.ofCoordinates z) = z :=
  L.coordinates.apply_symm_apply z

/-- Coordinate reconstruction is a right inverse. -/
@[simp]
theorem ofCoordinates_coordinates (L : RankTwoLattice E) (x : L.carrier) :
    L.ofCoordinates (L.coordinates x) = x :=
  L.coordinates.symm_apply_apply x

/-- A chosen basis vector has the corresponding standard integer coordinate. -/
@[simp]
theorem coordinates_basis (L : RankTwoLattice E) (i : Fin 2) :
    L.coordinates (L.basis i) = Pi.single i 1 := by
  classical
  funext j
  simp [coordinates, Pi.single_apply, eq_comm]

/-- Reconstructing coordinates is the finite linear combination of the chosen basis. -/
theorem ofCoordinates_apply (L : RankTwoLattice E) (z : Fin 2 → ℤ) :
    L.ofCoordinates z = ∑ i, z i • L.basis i := by
  exact L.basis.equivFun_symm_apply z

/-- Every lattice element expands uniquely in the chosen integer basis. -/
theorem basis_expansion (L : RankTwoLattice E) (x : L.carrier) :
    ∑ i, L.coordinates x i • L.basis i = x :=
  L.basis.sum_equivFun x

/-- Replace the chosen frame while retaining the same integer carrier. -/
def reframe (L : RankTwoLattice E) (b : Module.Basis (Fin 2) ℤ L.carrier)
    (hb : LinearIndependent ℝ (fun i => (b i : E))) : RankTwoLattice E where
  carrier := L.carrier
  basis := b
  basis_real_linearIndependent := hb

/-- Reframing leaves the integer carrier unchanged. -/
@[simp]
theorem reframe_carrier (L : RankTwoLattice E) (b : Module.Basis (Fin 2) ℤ L.carrier)
    (hb : LinearIndependent ℝ (fun i => (b i : E))) :
    (L.reframe b hb).carrier = L.carrier :=
  rfl

/-- Reframing installs exactly the supplied integer basis. -/
@[simp]
theorem reframe_basis (L : RankTwoLattice E) (b : Module.Basis (Fin 2) ℤ L.carrier)
    (hb : LinearIndependent ℝ (fun i => (b i : E))) :
    (L.reframe b hb).basis = b :=
  rfl

/-- Transport a lattice along an ambient real-linear equivalence. -/
def map (L : RankTwoLattice E) (e : E ≃ₗ[ℝ] E') : RankTwoLattice E' where
  carrier := L.carrier.map (e.restrictScalars ℤ : E →ₗ[ℤ] E')
  basis := L.basis.map ((e.restrictScalars ℤ).submoduleMap L.carrier)
  basis_real_linearIndependent := by
    have h := L.basis_real_linearIndependent.map' e.toLinearMap (by simp)
    simpa only [Function.comp_def, Module.Basis.map_apply,
      LinearEquiv.submoduleMap_apply, LinearEquiv.restrictScalars_apply,
      LinearEquiv.coe_coe] using h

/-- Transported basis vectors are the ambient images of the original basis vectors. -/
@[simp]
theorem map_basis_apply (L : RankTwoLattice E) (e : E ≃ₗ[ℝ] E') (i : Fin 2) :
    ((L.map e).basis i : E') = e (L.basis i : E) :=
  rfl

/-- The standard copy of `ℤ²` inside the Euclidean plane. -/
def standardCarrier : Submodule ℤ Plane :=
  Submodule.span ℤ (Set.range Plane.canonicalRealBasis)

/-- The canonical real coordinate frame, restricted to the standard integer lattice. -/
def standardBasis : Module.Basis (Fin 2) ℤ standardCarrier :=
  Plane.canonicalRealBasis.restrictScalars ℤ

/-- The standard framed rank-two lattice in the Euclidean plane. -/
def standardLattice : RankTwoLattice Plane where
  carrier := standardCarrier
  basis := standardBasis
  basis_real_linearIndependent := by
    have h : (fun i => ((standardBasis i : standardCarrier) : Plane)) =
        Plane.canonicalRealBasis := by
      funext i
      exact Module.Basis.restrictScalars_apply ℤ Plane.canonicalRealBasis i
    rw [h]
    exact Plane.canonicalRealBasis.linearIndependent

/-- Compatibility alias retaining the explicit rank-two-lattice name. -/
abbrev standardRankTwoLattice : RankTwoLattice Plane :=
  standardLattice

/-- The chosen integer basis of a plane lattice, regarded as a real basis of the plane. -/
def realBasis (L : RankTwoLattice Plane) : Module.Basis (Fin 2) ℝ Plane :=
  basisOfLinearIndependentOfCardEqFinrank
    L.basis_real_linearIndependent
    (by simp)

/-- The derived real basis has the same ambient vectors as the chosen integer basis. -/
@[simp]
theorem realBasis_apply (L : RankTwoLattice Plane) (i : Fin 2) :
    L.realBasis i = (L.basis i : Plane) := by
  simp [realBasis]

/-- Every rank-two plane lattice spans the full ambient plane over the reals. -/
theorem real_span_eq_top (L : RankTwoLattice Plane) :
    Submodule.span ℝ (L.carrier : Set Plane) = ⊤ := by
  apply top_unique
  rw [← L.realBasis.span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  rw [L.realBasis_apply]
  exact (L.basis i).property

/-! ## Integral matrices and `GL₂(ℤ)` -/

/-- The integer matrix of a lattice equivalence in the chosen source and target bases. -/
def equivMatrix (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) : Matrix (Fin 2) (Fin 2) ℤ :=
  LinearMap.toMatrix L.basis L'.basis f.toLinearMap

/--
Entries of an equivalence matrix are the target coordinates of images of source basis vectors.
-/
@[simp]
theorem equivMatrix_apply (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) (i j : Fin 2) :
    L.equivMatrix L' f i j = L'.basis.repr (f (L.basis j)) i :=
  LinearMap.toMatrix_apply L.basis L'.basis f.toLinearMap i j

/-- Matrix multiplication computes the target coordinates of an image. -/
theorem equivMatrix_apply_coordinates (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) (x : L.carrier) :
    Matrix.mulVec (L.equivMatrix L' f) (L.coordinates x) = L'.coordinates (f x) := by
  change Matrix.mulVec (LinearMap.toMatrix L.basis L'.basis f.toLinearMap)
      (L.basis.repr x) = L'.basis.repr (f.toLinearMap x)
  exact LinearMap.toMatrix_mulVec_repr L.basis L'.basis f.toLinearMap x

/-- The identity lattice equivalence has identity matrix. -/
@[simp]
theorem equivMatrix_refl (L : RankTwoLattice E) :
    L.equivMatrix L (LinearEquiv.refl ℤ L.carrier) = 1 := by
  simp [equivMatrix]

/-- Matrix coordinates reverse the written order of `LinearEquiv.trans`. -/
theorem equivMatrix_trans (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (L'' : RankTwoLattice E'') (f : L.carrier ≃ₗ[ℤ] L'.carrier)
    (g : L'.carrier ≃ₗ[ℤ] L''.carrier) :
    L.equivMatrix L'' (f.trans g) = L'.equivMatrix L'' g * L.equivMatrix L' f := by
  unfold equivMatrix
  rw [← LinearMap.toMatrix_comp]
  rfl

/-- An equivalence matrix followed by its inverse matrix is the identity. -/
@[simp]
theorem equivMatrix_mul_symm (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    L.equivMatrix L' f * L'.equivMatrix L f.symm = 1 := by
  unfold equivMatrix
  rw [← LinearMap.toMatrix_comp]
  simp

/-- The inverse matrix followed by the original equivalence matrix is the identity. -/
@[simp]
theorem equivMatrix_symm_mul (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    L'.equivMatrix L f.symm * L.equivMatrix L' f = 1 := by
  unfold equivMatrix
  rw [← LinearMap.toMatrix_comp]
  simp

/-- A lattice equivalence as an element of `GL₂(ℤ)`. -/
def equivGL (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) : Matrix.GeneralLinearGroup (Fin 2) ℤ where
  val := L.equivMatrix L' f
  inv := L'.equivMatrix L f.symm
  val_inv := L.equivMatrix_mul_symm L' f
  inv_val := L.equivMatrix_symm_mul L' f

/-- Coercing the bundled `GL₂(ℤ)` element recovers the equivalence matrix. -/
@[simp]
theorem coe_equivGL (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    (L.equivGL L' f : Matrix (Fin 2) (Fin 2) ℤ) = L.equivMatrix L' f :=
  rfl

/-- The matrix of the inverse equivalence is the inverse of the bundled `GL₂(ℤ)` element. -/
@[simp]
theorem equivMatrix_symm (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    L'.equivMatrix L f.symm =
      (↑((L.equivGL L' f)⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) :=
  rfl

/-- The identity equivalence gives the identity element of `GL₂(ℤ)`. -/
@[simp]
theorem equivGL_refl (L : RankTwoLattice E) :
    L.equivGL L (LinearEquiv.refl ℤ L.carrier) = 1 := by
  apply Units.ext
  exact L.equivMatrix_refl

/-- Composition of lattice equivalences becomes multiplication in `GL₂(ℤ)`. -/
theorem equivGL_trans (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (L'' : RankTwoLattice E'') (f : L.carrier ≃ₗ[ℤ] L'.carrier)
    (g : L'.carrier ≃ₗ[ℤ] L''.carrier) :
    L.equivGL L'' (f.trans g) = L'.equivGL L'' g * L.equivGL L' f := by
  apply Units.ext
  exact L.equivMatrix_trans L' L'' f g

/-- Taking the inverse lattice equivalence agrees with inversion in `GL₂(ℤ)`. -/
@[simp]
theorem equivGL_symm (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    L'.equivGL L f.symm = (L.equivGL L' f)⁻¹ := by
  apply Units.ext
  rfl

/-- Matrix coordinates faithfully determine a lattice equivalence. -/
theorem equivGL_injective (L : RankTwoLattice E) (L' : RankTwoLattice E') :
    Function.Injective (L.equivGL L') := by
  intro f g h
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix L.basis L'.basis).injective
  exact congrArg (↑· : Matrix.GeneralLinearGroup (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) ℤ) h

/-! ## Intertwining, commutation, and change of basis -/

/-- An intertwining relation of lattice automorphisms becomes the corresponding matrix identity. -/
theorem matrix_intertwining (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) (a : L.carrier ≃ₗ[ℤ] L.carrier)
    (b : L'.carrier ≃ₗ[ℤ] L'.carrier)
    (h : f.toLinearMap.comp a.toLinearMap = b.toLinearMap.comp f.toLinearMap) :
    L.equivMatrix L' f * L.equivMatrix L a =
      L'.equivMatrix L' b * L.equivMatrix L' f := by
  calc
    L.equivMatrix L' f * L.equivMatrix L a =
        LinearMap.toMatrix L.basis L'.basis
          (f.toLinearMap.comp a.toLinearMap) := by
      exact (LinearMap.toMatrix_comp
        L.basis L.basis L'.basis f.toLinearMap a.toLinearMap).symm
    _ = LinearMap.toMatrix L.basis L'.basis
          (b.toLinearMap.comp f.toLinearMap) := by rw [h]
    _ = L'.equivMatrix L' b * L.equivMatrix L' f := by
      exact LinearMap.toMatrix_comp
        L.basis L'.basis L'.basis b.toLinearMap f.toLinearMap

/-- A pointwise intertwining identity implies the bundled matrix intertwining identity. -/
theorem matrix_intertwining_of_apply (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) (a : L.carrier ≃ₗ[ℤ] L.carrier)
    (b : L'.carrier ≃ₗ[ℤ] L'.carrier)
    (h : ∀ x, f (a x) = b (f x)) :
    L.equivMatrix L' f * L.equivMatrix L a =
      L'.equivMatrix L' b * L.equivMatrix L' f := by
  apply L.matrix_intertwining L' f a b
  ext x
  exact congrArg (fun y : L'.carrier => (y : E')) (h x)

/-- Commuting lattice automorphisms have commuting matrices in every chosen frame. -/
theorem matrix_commutation (L : RankTwoLattice E)
    (a b : L.carrier ≃ₗ[ℤ] L.carrier)
    (h : a.toLinearMap.comp b.toLinearMap = b.toLinearMap.comp a.toLinearMap) :
    L.equivMatrix L a * L.equivMatrix L b =
      L.equivMatrix L b * L.equivMatrix L a := by
  simpa using L.matrix_intertwining L a b b h

/-- Intertwining lattice automorphisms have conjugate integer matrices. -/
theorem matrix_conjugacy (L : RankTwoLattice E) (L' : RankTwoLattice E')
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) (a : L.carrier ≃ₗ[ℤ] L.carrier)
    (b : L'.carrier ≃ₗ[ℤ] L'.carrier)
    (h : f.toLinearMap.comp a.toLinearMap = b.toLinearMap.comp f.toLinearMap) :
    L'.equivMatrix L' b =
      L.equivMatrix L' f * L.equivMatrix L a * L'.equivMatrix L f.symm := by
  have hi := L.matrix_intertwining L' f a b h
  calc
    L'.equivMatrix L' b = L'.equivMatrix L' b * 1 := (mul_one _).symm
    _ = L'.equivMatrix L' b *
        (L.equivMatrix L' f * L'.equivMatrix L f.symm) := by
      rw [L.equivMatrix_mul_symm L' f]
    _ = (L'.equivMatrix L' b * L.equivMatrix L' f) *
        L'.equivMatrix L f.symm := by rw [mul_assoc]
    _ = (L.equivMatrix L' f * L.equivMatrix L a) *
        L'.equivMatrix L f.symm := by rw [hi]
    _ = L.equivMatrix L' f * L.equivMatrix L a *
        L'.equivMatrix L f.symm := rfl

/-- The matrix converting old lattice coordinates to a supplied new frame. -/
def basisChangeMatrix (L : RankTwoLattice E) (b : Module.Basis (Fin 2) ℤ L.carrier)
    (hb : LinearIndependent ℝ (fun i => (b i : E))) : Matrix (Fin 2) (Fin 2) ℤ :=
  L.equivMatrix (L.reframe b hb) (LinearEquiv.refl ℤ L.carrier)

/-- The coordinate change bundled as an element of `GL₂(ℤ)`. -/
def basisChangeGL (L : RankTwoLattice E) (b : Module.Basis (Fin 2) ℤ L.carrier)
    (hb : LinearIndependent ℝ (fun i => (b i : E))) :
    Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  L.equivGL (L.reframe b hb) (LinearEquiv.refl ℤ L.carrier)

/-- Reframing conjugates every automorphism matrix by the coordinate-change matrix. -/
theorem matrix_conjugacy_reframe (L : RankTwoLattice E)
    (b : Module.Basis (Fin 2) ℤ L.carrier)
    (hb : LinearIndependent ℝ (fun i => (b i : E)))
    (a : L.carrier ≃ₗ[ℤ] L.carrier) :
    (L.reframe b hb).equivMatrix (L.reframe b hb) a =
      L.basisChangeMatrix b hb * L.equivMatrix L a *
        (L.reframe b hb).equivMatrix L (LinearEquiv.refl ℤ L.carrier) := by
  apply L.matrix_conjugacy (L.reframe b hb) (LinearEquiv.refl ℤ L.carrier) a a
  ext x
  rfl

/-! ## Extension of lattice equivalences to the real plane -/

/-- Cast the integer matrix of a plane-lattice equivalence to a real matrix. -/
def realEquivMatrix (L L' : RankTwoLattice Plane)
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) : Matrix (Fin 2) (Fin 2) ℝ :=
  (L.equivMatrix L' f).map (Int.castRingHom ℝ)

/-- The cast matrix followed by the cast inverse matrix is the identity. -/
@[simp]
theorem realEquivMatrix_mul_symm (L L' : RankTwoLattice Plane)
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    L.realEquivMatrix L' f * L'.realEquivMatrix L f.symm = 1 := by
  unfold realEquivMatrix
  rw [← Matrix.map_mul]
  rw [L.equivMatrix_mul_symm L' f]
  simp

/-- The cast inverse matrix followed by the cast original matrix is the identity. -/
@[simp]
theorem realEquivMatrix_symm_mul (L L' : RankTwoLattice Plane)
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    L'.realEquivMatrix L f.symm * L.realEquivMatrix L' f = 1 := by
  unfold realEquivMatrix
  rw [← Matrix.map_mul]
  rw [L.equivMatrix_symm_mul L' f]
  simp

/--
Extend an arbitrary integer-linear lattice equivalence uniquely through the chosen real bases.
-/
def extendEquiv (L L' : RankTwoLattice Plane)
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) : Plane ≃ₗ[ℝ] Plane :=
  Matrix.toLinOfInv L.realBasis L'.realBasis
    (M := L.realEquivMatrix L' f)
    (M' := L'.realEquivMatrix L f.symm)
    (L.realEquivMatrix_mul_symm L' f)
    (L.realEquivMatrix_symm_mul L' f)

/-- The real extension agrees with the lattice equivalence on every chosen basis vector. -/
@[simp]
theorem extendEquiv_basis (L L' : RankTwoLattice Plane)
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) (i : Fin 2) :
    L.extendEquiv L' f (L.basis i : Plane) =
      ((f (L.basis i) : L'.carrier) : Plane) := by
  unfold extendEquiv
  rw [← L.realBasis_apply i]
  rw [Matrix.toLinOfInv_apply, Matrix.toLin_self]
  have h := congrArg (fun y : L'.carrier => (y : Plane))
    (L'.basis.sum_repr (f (L.basis i)))
  rw [← h]
  change ∑ j, L.realEquivMatrix L' f j i • L'.realBasis j =
    L'.carrier.subtype (∑ j, (L'.basis.repr (f (L.basis i))) j • L'.basis j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [realEquivMatrix, equivMatrix, LinearMap.toMatrix_apply,
    realBasis_apply, Int.cast_smul_eq_zsmul ℝ]

/-- The real extension agrees with the integer equivalence on every lattice element. -/
@[simp]
theorem extendEquiv_agrees (L L' : RankTwoLattice Plane)
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) (x : L.carrier) :
    L.extendEquiv L' f (x : Plane) = ((f x : L'.carrier) : Plane) := by
  let lhs : L.carrier →ₗ[ℤ] Plane :=
    (L.extendEquiv L' f).toLinearMap.restrictScalars ℤ |>.comp L.carrier.subtype
  let rhs : L.carrier →ₗ[ℤ] Plane :=
    L'.carrier.subtype.comp f.toLinearMap
  have h : lhs = rhs := L.basis.ext fun i => by
    simp [lhs, rhs, L.extendEquiv_basis L' f]
  exact LinearMap.congr_fun h x

/-- Extending the inverse lattice equivalence gives the inverse real-linear equivalence. -/
@[simp]
theorem extendEquiv_symm (L L' : RankTwoLattice Plane)
    (f : L.carrier ≃ₗ[ℤ] L'.carrier) :
    L'.extendEquiv L f.symm = (L.extendEquiv L' f).symm := by
  apply LinearEquiv.toLinearMap_injective
  apply L'.realBasis.ext
  intro i
  change L'.extendEquiv L f.symm (L'.realBasis i) =
    (L.extendEquiv L' f).symm (L'.realBasis i)
  rw [L'.realBasis_apply, L'.extendEquiv_agrees L f.symm]
  apply (L.extendEquiv L' f).eq_symm_apply.mpr
  rw [L.extendEquiv_agrees L' f]
  simp

/-- Extending the identity lattice equivalence gives the identity of the real plane. -/
@[simp]
theorem extendEquiv_refl (L : RankTwoLattice Plane) :
    L.extendEquiv L (LinearEquiv.refl ℤ L.carrier) = LinearEquiv.refl ℝ Plane := by
  apply LinearEquiv.toLinearMap_injective
  apply L.realBasis.ext
  intro i
  rw [L.realBasis_apply]
  simp

/-- Real extension preserves composition of lattice equivalences. -/
theorem extendEquiv_trans (L L' L'' : RankTwoLattice Plane)
    (f : L.carrier ≃ₗ[ℤ] L'.carrier)
    (g : L'.carrier ≃ₗ[ℤ] L''.carrier) :
    L.extendEquiv L'' (f.trans g) = (L.extendEquiv L' f).trans (L'.extendEquiv L'' g) := by
  apply LinearEquiv.toLinearMap_injective
  apply L.realBasis.ext
  intro i
  rw [L.realBasis_apply]
  simp

end RankTwoLattice

end


end WallpaperGroups
