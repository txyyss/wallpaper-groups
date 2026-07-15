import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import WallpaperGroups.Invariants.IntegralAction
import WallpaperGroups.Restriction.Orientation

set_option linter.style.header false

/-!
# The two-dimensional crystallographic restriction

This file implements the integer-trace and Cayley–Hamilton proof that every
orientation-preserving element of a plane point group has order `1`, `2`, `3`, `4`, or `6`.
The public trace bridge relates the integral lattice action to the ambient real isometry, while
the exact `GL₂(ℤ)` order lemmas provide reusable algebraic input for later lattice normal forms.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-! ## The finite set of possible rotation orders -/

/-- The five orders allowed by the two-dimensional crystallographic restriction. -/
inductive CrystallographicOrder where
  /-- Trivial rotation order. -/
  | one
  /-- Half-turn order. -/
  | two
  /-- Third-turn order. -/
  | three
  /-- Quarter-turn order. -/
  | four
  /-- Sixth-turn order. -/
  | six
  deriving DecidableEq, Fintype

namespace CrystallographicOrder

/-- Interpret a crystallographic order as its natural-number value. -/
def toNat : CrystallographicOrder → ℕ
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .six => 6

end CrystallographicOrder

/-- A natural number is an allowed two-dimensional crystallographic rotation order. -/
def IsCrystallographicOrder (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6

/-- The predicate of allowed orders is exactly membership in the typed five-element list. -/
theorem isCrystallographicOrder_iff_exists_toNat (n : ℕ) :
    IsCrystallographicOrder n ↔
      ∃ q : CrystallographicOrder, n = q.toNat := by
  constructor
  · rintro (h | h | h | h | h)
    · exact ⟨.one, h⟩
    · exact ⟨.two, h⟩
    · exact ⟨.three, h⟩
    · exact ⟨.four, h⟩
    · exact ⟨.six, h⟩
  · rintro ⟨q, rfl⟩
    cases q <;> simp [IsCrystallographicOrder, CrystallographicOrder.toNat]

/-! ## Integral and ambient trace bridges -/

namespace PlaneGroup

variable (G : PlaneGroup) (h : pointGroup G.carrier)

/--
The real cast of the lattice-action matrix is the matrix of the ambient plane isometry in the
real basis induced by the translation lattice.
-/
theorem realMatrix_eq_ambientMatrix :
    G.translationLattice.realEquivMatrix G.translationLattice (G.latticeAction h) =
      LinearMap.toMatrix G.realBasis G.realBasis
        (h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap := by
  have hext : G.translationLattice.extendEquiv G.translationLattice
      (G.latticeAction h) = (h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv := by
    apply LinearEquiv.toLinearMap_injective
    apply G.realBasis.ext
    intro i
    rw [RankTwoLattice.realBasis_apply]
    change G.translationLattice.extendEquiv G.translationLattice
        (G.latticeAction h) (G.translationLattice.basis i : Plane) = _
    rw [RankTwoLattice.extendEquiv_basis]
    exact G.latticeAction_coe h (G.translationLattice.basis i)
  rw [← hext]
  symm
  unfold RankTwoLattice.extendEquiv
  exact LinearMap.toMatrix_toLin _ _ _

/-- The integer trace of a lattice action casts to the real trace of the ambient isometry. -/
theorem trace_cast :
    ((G.latticeActionMatrix h).trace : ℝ) =
      LinearMap.trace ℝ Plane
        (h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ G.realBasis]
  rw [← G.realMatrix_eq_ambientMatrix h]
  exact AddMonoidHom.map_trace (Int.castRingHom ℝ) (G.latticeActionMatrix h)

/-- The integer determinant of a lattice action casts to the determinant of the ambient map. -/
theorem det_cast :
    ((G.latticeActionMatrix h).det : ℝ) =
      LinearMap.det
        (h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap := by
  rw [← LinearMap.det_toMatrix G.realBasis]
  rw [← G.realMatrix_eq_ambientMatrix h]
  exact RingHom.map_det (Int.castRingHom ℝ) (G.latticeActionMatrix h)

end PlaneGroup

/-! ## Trace bounds and their extremal cases -/

/-- The real trace of a plane linear isometry lies in the interval `[-2, 2]`. -/
theorem trace_bounds (phi : Plane ≃ₗᵢ[ℝ] Plane) :
    -2 ≤ LinearMap.trace ℝ Plane phi.toLinearEquiv.toLinearMap ∧
      LinearMap.trace ℝ Plane phi.toLinearEquiv.toLinearMap ≤ 2 := by
  rw [LinearMap.trace_eq_sum_inner phi.toLinearEquiv.toLinearMap
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  rw [Fin.sum_univ_two]
  have h0 := real_inner_mem_Icc_of_norm_eq_one
    (EuclideanSpace.basisFun (Fin 2) ℝ |>.norm_eq_one 0)
    (by
      rw [phi.norm_map]
      exact EuclideanSpace.basisFun (Fin 2) ℝ |>.norm_eq_one 0)
  change -1 ≤ ⟪(EuclideanSpace.basisFun (Fin 2) ℝ) 0,
      phi.toLinearEquiv.toLinearMap ((EuclideanSpace.basisFun (Fin 2) ℝ) 0)⟫_ℝ ∧
    ⟪(EuclideanSpace.basisFun (Fin 2) ℝ) 0,
      phi.toLinearEquiv.toLinearMap ((EuclideanSpace.basisFun (Fin 2) ℝ) 0)⟫_ℝ ≤ 1 at h0
  have h1 := real_inner_mem_Icc_of_norm_eq_one
    (EuclideanSpace.basisFun (Fin 2) ℝ |>.norm_eq_one 1)
    (by
      rw [phi.norm_map]
      exact EuclideanSpace.basisFun (Fin 2) ℝ |>.norm_eq_one 1)
  change -1 ≤ ⟪(EuclideanSpace.basisFun (Fin 2) ℝ) 1,
      phi.toLinearEquiv.toLinearMap ((EuclideanSpace.basisFun (Fin 2) ℝ) 1)⟫_ℝ ∧
    ⟪(EuclideanSpace.basisFun (Fin 2) ℝ) 1,
      phi.toLinearEquiv.toLinearMap ((EuclideanSpace.basisFun (Fin 2) ℝ) 1)⟫_ℝ ≤ 1 at h1
  constructor <;> linarith

/-- A plane linear isometry with trace `2` is the identity. -/
theorem eq_one_of_trace_eq_two (phi : Plane ≃ₗᵢ[ℝ] Plane)
    (htrace : LinearMap.trace ℝ Plane phi.toLinearEquiv.toLinearMap = 2) :
    phi = 1 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let T := phi.toLinearEquiv.toLinearMap
  have hsum := LinearMap.trace_eq_sum_inner T b
  change LinearMap.trace ℝ Plane T = 2 at htrace
  rw [htrace, Fin.sum_univ_two] at hsum
  have h0 := real_inner_mem_Icc_of_norm_eq_one (b.norm_eq_one 0) (by
    change ‖phi (b 0)‖ = 1
    rw [phi.norm_map]
    exact b.norm_eq_one 0)
  have h1 := real_inner_mem_Icc_of_norm_eq_one (b.norm_eq_one 1) (by
    change ‖phi (b 1)‖ = 1
    rw [phi.norm_map]
    exact b.norm_eq_one 1)
  change -1 ≤ ⟪b 0, T (b 0)⟫_ℝ ∧ ⟪b 0, T (b 0)⟫_ℝ ≤ 1 at h0
  change -1 ≤ ⟪b 1, T (b 1)⟫_ℝ ∧ ⟪b 1, T (b 1)⟫_ℝ ≤ 1 at h1
  have heq0 : ⟪b 0, T (b 0)⟫_ℝ = 1 := by linarith
  have heq1 : ⟪b 1, T (b 1)⟫_ℝ = 1 := by linarith
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply b.toBasis.ext
  intro i
  fin_cases i
  · change T (b 0) = LinearMap.id (b 0)
    rw [LinearMap.id_apply]
    exact (inner_eq_one_iff_of_norm_eq_one (b.norm_eq_one 0) (by
      change ‖phi (b 0)‖ = 1
      rw [phi.norm_map]
      exact b.norm_eq_one 0)).mp heq0 |>.symm
  · change T (b 1) = LinearMap.id (b 1)
    rw [LinearMap.id_apply]
    exact (inner_eq_one_iff_of_norm_eq_one (b.norm_eq_one 1) (by
      change ‖phi (b 1)‖ = 1
      rw [phi.norm_map]
      exact b.norm_eq_one 1)).mp heq1 |>.symm

/-- A plane linear isometry with trace `-2` is central inversion. -/
theorem eq_neg_of_trace_eq_neg_two (phi : Plane ≃ₗᵢ[ℝ] Plane)
    (htrace : LinearMap.trace ℝ Plane phi.toLinearEquiv.toLinearMap = -2) :
    phi = LinearIsometryEquiv.neg ℝ := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let T := phi.toLinearEquiv.toLinearMap
  have hsum := LinearMap.trace_eq_sum_inner T b
  change LinearMap.trace ℝ Plane T = -2 at htrace
  rw [htrace, Fin.sum_univ_two] at hsum
  have h0 := real_inner_mem_Icc_of_norm_eq_one (b.norm_eq_one 0) (by
    change ‖phi (b 0)‖ = 1
    rw [phi.norm_map]
    exact b.norm_eq_one 0)
  have h1 := real_inner_mem_Icc_of_norm_eq_one (b.norm_eq_one 1) (by
    change ‖phi (b 1)‖ = 1
    rw [phi.norm_map]
    exact b.norm_eq_one 1)
  change -1 ≤ ⟪b 0, T (b 0)⟫_ℝ ∧ ⟪b 0, T (b 0)⟫_ℝ ≤ 1 at h0
  change -1 ≤ ⟪b 1, T (b 1)⟫_ℝ ∧ ⟪b 1, T (b 1)⟫_ℝ ≤ 1 at h1
  have heq0 : ⟪b 0, T (b 0)⟫_ℝ = -1 := by linarith
  have heq1 : ⟪b 1, T (b 1)⟫_ℝ = -1 := by linarith
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply b.toBasis.ext
  intro i
  fin_cases i
  · change T (b 0) = -(b 0)
    have he := (inner_eq_neg_one_iff_of_norm_eq_one (b.norm_eq_one 0) (by
      change ‖phi (b 0)‖ = 1
      rw [phi.norm_map]
      exact b.norm_eq_one 0)).mp heq0
    have hneg := congrArg Neg.neg he
    simpa using hneg.symm
  · change T (b 1) = -(b 1)
    have he := (inner_eq_neg_one_iff_of_norm_eq_one (b.norm_eq_one 1) (by
      change ‖phi (b 1)‖ = 1
      rw [phi.norm_map]
      exact b.norm_eq_one 1)).mp heq1
    have hneg := congrArg Neg.neg he
    simpa using hneg.symm

/-! ## Basis invariance and exact `GL₂(ℤ)` orders -/

/-- The group `GL₂(ℤ)` represented by invertible `2 × 2` integer matrices. -/
abbrev GL2Z := Matrix.GeneralLinearGroup (Fin 2) ℤ

/-- Reframing a rank-two lattice does not change the trace of an automorphism matrix. -/
theorem trace_reframe_invariant (L : RankTwoLattice Plane)
    (b : Module.Basis (Fin 2) ℤ L.carrier)
    (hb : LinearIndependent ℝ (fun i => (b i : Plane)))
    (a : L.carrier ≃ₗ[ℤ] L.carrier) :
    (L.equivMatrix L a).trace =
      ((L.reframe b hb).equivMatrix (L.reframe b hb) a).trace := by
  calc
    (L.equivMatrix L a).trace =
        LinearMap.trace ℤ L.carrier a.toLinearMap :=
      (LinearMap.trace_eq_matrix_trace ℤ L.basis a.toLinearMap).symm
    _ = ((L.reframe b hb).equivMatrix (L.reframe b hb) a).trace :=
      LinearMap.trace_eq_matrix_trace ℤ b a.toLinearMap

/-- Reframing a rank-two lattice does not change the determinant of an automorphism matrix. -/
theorem det_reframe_invariant (L : RankTwoLattice Plane)
    (b : Module.Basis (Fin 2) ℤ L.carrier)
    (hb : LinearIndependent ℝ (fun i => (b i : Plane)))
    (a : L.carrier ≃ₗ[ℤ] L.carrier) :
    (L.equivMatrix L a).det =
      ((L.reframe b hb).equivMatrix (L.reframe b hb) a).det := by
  calc
    (L.equivMatrix L a).det = LinearMap.det a.toLinearMap :=
      LinearMap.det_toMatrix L.basis a.toLinearMap
    _ = ((L.reframe b hb).equivMatrix (L.reframe b hb) a).det :=
      (LinearMap.det_toMatrix b a.toLinearMap).symm

/-- Cayley–Hamilton for a `2 × 2` integer matrix in trace-determinant form. -/
theorem cayley_hamilton (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A ^ 2 - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) = 0 := by
  have h := Matrix.aeval_self_charpoly A
  rw [Matrix.charpoly_fin_two] at h
  simpa [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.smul_def, smul_eq_mul] using h

/-- A determinant-one `GL₂(ℤ)` matrix of trace `-1` has exact order `3`. -/
theorem order_three (U : GL2Z)
    (htrace : (U : Matrix (Fin 2) (Fin 2) ℤ).trace = -1)
    (hdet : (U : Matrix (Fin 2) (Fin 2) ℤ).det = 1) :
    orderOf U = 3 := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := U
  have hp : A ^ 2 + A + 1 = 0 := by
    simpa [A, htrace, hdet] using cayley_hamilton A
  have hA3 : A ^ 3 = 1 := by
    apply sub_eq_zero.mp
    calc
      A ^ 3 - 1 = (A - 1) * (A ^ 2 + A + 1) := by noncomm_ring
      _ = 0 := by rw [hp, mul_zero]
  have hU3 : U ^ 3 = 1 := by
    apply Units.ext
    exact hA3
  have hUne : U ≠ 1 := by
    intro hU
    have ht := congrArg (fun V : GL2Z =>
      (V : Matrix (Fin 2) (Fin 2) ℤ).trace) hU
    rw [htrace] at ht
    norm_num at ht
  exact orderOf_eq_prime hU3 hUne

/-- A determinant-one `GL₂(ℤ)` matrix of trace `0` has exact order `4`. -/
theorem order_four (U : GL2Z)
    (htrace : (U : Matrix (Fin 2) (Fin 2) ℤ).trace = 0)
    (hdet : (U : Matrix (Fin 2) (Fin 2) ℤ).det = 1) :
    orderOf U = 4 := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := U
  have hp : A ^ 2 + 1 = 0 := by
    simpa [A, htrace, hdet] using cayley_hamilton A
  have hA2 : A ^ 2 = -1 := eq_neg_of_add_eq_zero_left hp
  have hU2 : U ^ 2 ≠ 1 := by
    intro h
    have hv := congrArg (fun V : GL2Z =>
      (V : Matrix (Fin 2) (Fin 2) ℤ)) h
    rw [Units.val_pow_eq_pow_val] at hv
    rw [hA2] at hv
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hv
    norm_num at hentry
  have hU4 : U ^ 4 = 1 := by
    apply Units.ext
    change A ^ 4 = 1
    calc
      A ^ 4 = (A ^ 2) ^ 2 := by noncomm_ring
      _ = 1 := by rw [hA2]; simp
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hU4
  intro p hpprime hpdiv
  have hp2pow : p ∣ 2 ^ 2 := by
    norm_num
    exact hpdiv
  have hp2dvd : p ∣ 2 := hpprime.dvd_of_dvd_pow hp2pow
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp hp2dvd
  subst p
  norm_num
  exact hU2

/-- A determinant-one `GL₂(ℤ)` matrix of trace `1` has exact order `6`. -/
theorem order_six (U : GL2Z)
    (htrace : (U : Matrix (Fin 2) (Fin 2) ℤ).trace = 1)
    (hdet : (U : Matrix (Fin 2) (Fin 2) ℤ).det = 1) :
    orderOf U = 6 := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := U
  have hp : A ^ 2 - A + 1 = 0 := by
    simpa [A, htrace, hdet] using cayley_hamilton A
  have hA3 : A ^ 3 = -1 := by
    apply eq_neg_of_add_eq_zero_left
    calc
      A ^ 3 + 1 = (A + 1) * (A ^ 2 - A + 1) := by noncomm_ring
      _ = 0 := by rw [hp, mul_zero]
  have hU3 : U ^ 3 ≠ 1 := by
    intro h
    have hv := congrArg (fun V : GL2Z =>
      (V : Matrix (Fin 2) (Fin 2) ℤ)) h
    rw [Units.val_pow_eq_pow_val] at hv
    rw [hA3] at hv
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hv
    norm_num at hentry
  have hU2 : U ^ 2 ≠ 1 := by
    intro h
    have hv := congrArg (fun V : GL2Z =>
      (V : Matrix (Fin 2) (Fin 2) ℤ)) h
    rw [Units.val_pow_eq_pow_val] at hv
    change A ^ 2 = 1 at hv
    have hc := congrArg Matrix.trace hp
    rw [hv] at hc
    simp [A, htrace] at hc
  have hU6 : U ^ 6 = 1 := by
    apply Units.ext
    change A ^ 6 = 1
    calc
      A ^ 6 = (A ^ 3) ^ 2 := by noncomm_ring
      _ = 1 := by rw [hA3]; simp
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hU6
  intro p hpprime hpdiv
  have hp23 : p ∣ 2 * 3 := by simpa using hpdiv
  rcases (hpprime.dvd_mul).mp hp23 with hp2dvd | hp3dvd
  · have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp hp2dvd
    subst p
    norm_num
    exact hU3
  · have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_three).mp hp3dvd
    subst p
    norm_num
    exact hU2

/-! ## The crystallographic restriction for point-group elements -/

namespace PlaneGroup

/-- The integral trace of any plane point-group element is one of `-2, -1, 0, 1, 2`. -/
theorem integral_trace_cases (G : PlaneGroup) (h : pointGroup G.carrier) :
    (G.latticeActionMatrix h).trace = -2 ∨
    (G.latticeActionMatrix h).trace = -1 ∨
    (G.latticeActionMatrix h).trace = 0 ∨
    (G.latticeActionMatrix h).trace = 1 ∨
    (G.latticeActionMatrix h).trace = 2 := by
  have hb := trace_bounds (h : Plane ≃ₗᵢ[ℝ] Plane)
  rw [← G.trace_cast h] at hb
  have hlo : (-2 : ℤ) ≤ (G.latticeActionMatrix h).trace := by
    exact_mod_cast hb.1
  have hhi : (G.latticeActionMatrix h).trace ≤ (2 : ℤ) := by
    exact_mod_cast hb.2
  omega

/-- A positive-determinant point-group element has determinant-one integral action. -/
theorem integral_det_eq_one (G : PlaneGroup) (h : pointGroup G.carrier)
    (hpos : 0 < LinearMap.det
      (h : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap) :
    (G.latticeActionMatrix h).det = 1 := by
  have hdR := positive_isometry_det_eq_one (h : Plane ≃ₗᵢ[ℝ] Plane) hpos
  have hc := G.det_cast h
  exact_mod_cast hc.trans hdR

/--
For an orientation-preserving point-group element, each possible integral trace is paired with
its exact point-group order.
-/
theorem orientationPreserving_trace_order_cases (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) :
    ((G.latticeActionMatrix h.1).trace = -2 ∧ orderOf h.1 = 2) ∨
    ((G.latticeActionMatrix h.1).trace = -1 ∧ orderOf h.1 = 3) ∨
    ((G.latticeActionMatrix h.1).trace = 0 ∧ orderOf h.1 = 4) ∨
    ((G.latticeActionMatrix h.1).trace = 1 ∧ orderOf h.1 = 6) ∨
    ((G.latticeActionMatrix h.1).trace = 2 ∧ orderOf h.1 = 1) := by
  let U := G.integralRepresentation h.1
  have hdet : (U : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    exact G.integral_det_eq_one h.1 (orientationPreserving_det_pos G h)
  have hord : orderOf U = orderOf h.1 := by
    exact orderOf_injective G.integralRepresentation
      G.integralRepresentation_injective h.1
  rcases G.integral_trace_cases h.1 with ht | ht | ht | ht | ht
  · left
    refine ⟨ht, ?_⟩
    have htR : LinearMap.trace ℝ Plane
        (h.1 : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap = -2 := by
      rw [← G.trace_cast h.1]
      exact_mod_cast ht
    have hneg := eq_neg_of_trace_eq_neg_two
      (h.1 : Plane ≃ₗᵢ[ℝ] Plane) htR
    have hh2 : h.1 ^ 2 = 1 := by
      apply Subtype.ext
      change (h.1 : Plane ≃ₗᵢ[ℝ] Plane) ^ 2 = 1
      rw [hneg]
      rw [pow_two]
      apply LinearIsometryEquiv.ext
      intro x
      change -(-x) = x
      simp
    have hU2 : U ^ 2 = 1 := by
      change (G.integralRepresentation h.1) ^ 2 = 1
      rw [← map_pow, hh2, map_one]
    have hUne : U ≠ 1 := by
      have htU : (U : Matrix (Fin 2) (Fin 2) ℤ).trace = -2 := ht
      intro hU
      rw [hU] at htU
      norm_num at htU
    exact hord.symm.trans (orderOf_eq_prime hU2 hUne)
  · right; left
    exact ⟨ht, hord.symm.trans (order_three U (by exact ht) hdet)⟩
  · right; right; left
    exact ⟨ht, hord.symm.trans (order_four U (by exact ht) hdet)⟩
  · right; right; right; left
    exact ⟨ht, hord.symm.trans (order_six U (by exact ht) hdet)⟩
  · right; right; right; right
    refine ⟨ht, ?_⟩
    have htR : LinearMap.trace ℝ Plane
        (h.1 : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap = 2 := by
      rw [← G.trace_cast h.1]
      exact_mod_cast ht
    have hone := eq_one_of_trace_eq_two
      (h.1 : Plane ≃ₗᵢ[ℝ] Plane) htR
    have hh : h.1 = 1 := by
      apply Subtype.ext
      exact hone
    exact orderOf_eq_one_iff.mpr hh

/-- The underlying point-group element of a positive rotation has one of the five allowed orders. -/
theorem orientationPreserving_point_order_cases (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) :
    orderOf h.1 = 1 ∨ orderOf h.1 = 2 ∨ orderOf h.1 = 3 ∨
      orderOf h.1 = 4 ∨ orderOf h.1 = 6 := by
  rcases G.orientationPreserving_trace_order_cases h with
    ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨_, h4⟩ | ⟨_, h6⟩ | ⟨_, h1⟩
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))
  · exact Or.inl h1

/-- The integral `GL₂(ℤ)` representation of a positive rotation has an allowed order. -/
theorem orientationPreserving_integralRepresentation_order_cases (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) :
    orderOf (G.integralRepresentation h.1) = 1 ∨
    orderOf (G.integralRepresentation h.1) = 2 ∨
    orderOf (G.integralRepresentation h.1) = 3 ∨
    orderOf (G.integralRepresentation h.1) = 4 ∨
    orderOf (G.integralRepresentation h.1) = 6 := by
  have hord := orderOf_injective G.integralRepresentation
    G.integralRepresentation_injective h.1
  rw [hord]
  exact G.orientationPreserving_point_order_cases h

/-- Every orientation-preserving point-group element has crystallographic order. -/
theorem orientationPreserving_order_isCrystallographic (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) :
    IsCrystallographicOrder (orderOf h.1) := by
  simpa [IsCrystallographicOrder] using G.orientationPreserving_point_order_cases h

/-- Typed form of the crystallographic restriction for one orientation-preserving element. -/
theorem orientationPreserving_order_eq_toNat (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) :
    ∃ q : CrystallographicOrder, orderOf h.1 = q.toNat :=
  (isCrystallographicOrder_iff_exists_toNat (orderOf h.1)).mp
    (G.orientationPreserving_order_isCrystallographic h)

/-- The order of the entire orientation-preserving point subgroup is crystallographic. -/
theorem orientationPreserving_subgroup_order_isCrystallographic (G : PlaneGroup) :
    IsCrystallographicOrder (Nat.card (orientationPreservingPointGroup G)) := by
  letI : IsCyclic (orientationPreservingPointGroup G) :=
    orientationPreserving_isCyclic G
  obtain ⟨h, hh⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard
      (α := orientationPreservingPointGroup G)
  rw [← hh]
  have hinj : Function.Injective (orientationPreservingPointGroup G).subtype := by
    intro a b hab
    exact Subtype.ext hab
  have hord : orderOf h.1 = orderOf h :=
    orderOf_injective (orientationPreservingPointGroup G).subtype hinj h
  rw [← hord]
  exact G.orientationPreserving_order_isCrystallographic h

/-- Typed form of the crystallographic restriction for the positive point subgroup itself. -/
theorem orientationPreserving_subgroup_order_eq_toNat (G : PlaneGroup) :
    ∃ q : CrystallographicOrder,
      Nat.card (orientationPreservingPointGroup G) = q.toNat :=
  (isCrystallographicOrder_iff_exists_toNat
    (Nat.card (orientationPreservingPointGroup G))).mp
      G.orientationPreserving_subgroup_order_isCrystallographic

/-- An orientation-preserving element of exact order `3` has integral trace `-1`. -/
theorem orientationPreserving_trace_eq_of_order_three (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) (horder : orderOf h.1 = 3) :
    (G.latticeActionMatrix h.1).trace = -1 := by
  rcases G.orientationPreserving_trace_order_cases h with
    ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩
  all_goals omega

/-- An orientation-preserving element of exact order `4` has integral trace `0`. -/
theorem orientationPreserving_trace_eq_of_order_four (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) (horder : orderOf h.1 = 4) :
    (G.latticeActionMatrix h.1).trace = 0 := by
  rcases G.orientationPreserving_trace_order_cases h with
    ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩
  all_goals omega

/-- An orientation-preserving element of exact order `6` has integral trace `1`. -/
theorem orientationPreserving_trace_eq_of_order_six (G : PlaneGroup)
    (h : orientationPreservingPointGroup G) (horder : orderOf h.1 = 6) :
    (G.latticeActionMatrix h.1).trace = 1 := by
  rcases G.orientationPreserving_trace_order_cases h with
    ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩ | ⟨ht, ho⟩
  all_goals omega

end PlaneGroup

end

end WallpaperGroups
