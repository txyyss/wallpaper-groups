import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Round
import WallpaperGroups.Basic.RankTwoLattice
import WallpaperGroups.Restriction.Crystallographic

set_option linter.style.header false

/-!
# Lattice normal forms for crystallographic rotations

This module derives a shortest nonzero vector in every framed rank-two plane lattice.  For a
determinant-one lattice isometry of trace `-1`, `0`, or `1`, nearest-integer reduction shows that
the orbit pair `(t, A t)` of a shortest vector is an integral basis.  In that basis the action is
the standard order-three, order-four, or order-six companion matrix used by later classification
milestones.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

namespace RankTwoLattice

/-- A framed rank-two plane lattice is the integer span of its derived real basis. -/
theorem carrier_eq_zspan_realBasis (L : RankTwoLattice Plane) :
    L.carrier = Submodule.span ℤ (Set.range L.realBasis) := by
  apply le_antisymm
  · intro x hx
    let y : L.carrier := ⟨x, hx⟩
    have hy := congrArg L.carrier.subtype (L.basis_expansion y)
    have hy' : ∑ i, L.coordinates y i • (L.basis i : Plane) = x := by
      simpa only [map_sum, map_zsmul, Submodule.coe_subtype] using hy
    rw [← hy']
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨i, (L.realBasis_apply i).trans rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    rw [L.realBasis_apply]
    exact (L.basis i).property

/-- A nonzero lattice vector of globally minimal norm. -/
structure ShortestVector (L : RankTwoLattice Plane) where
  /-- The selected lattice vector. -/
  vector : L.carrier
  /-- The selected vector is nonzero. -/
  ne_zero : vector ≠ 0
  /-- No nonzero lattice vector has smaller norm. -/
  minimal : ∀ s : L.carrier, s ≠ 0 → ‖(vector : Plane)‖ ≤ ‖(s : Plane)‖

/-- Every framed rank-two plane lattice has a shortest nonzero vector. -/
theorem exists_shortestVector (L : RankTwoLattice Plane) :
    Nonempty (ShortestVector L) := by
  let u : L.carrier := L.basis 0
  have hu : u ≠ 0 := by
    intro hu
    have hli := L.basis.linearIndependent
    exact hli.ne_zero 0 hu
  let S : Set Plane :=
    {x | x ∈ L.carrier ∧ x ≠ 0 ∧ ‖x‖ ≤ ‖(u : Plane)‖}
  have hSfinite : S.Finite := by
    have hfin := ZSpan.setFinite_inter L.realBasis
      (s := Metric.closedBall (0 : Plane) ‖(u : Plane)‖)
      Metric.isBounded_closedBall
    rw [← L.carrier_eq_zspan_realBasis] at hfin
    apply hfin.subset
    intro x hx
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hx.2.2, hx.1⟩
  have hSnonempty : S.Nonempty := by
    refine ⟨(u : Plane), u.property, ?_, le_rfl⟩
    exact_mod_cast hu
  obtain ⟨t, htS, htmin⟩ := Set.exists_min_image S norm hSfinite hSnonempty
  let tL : L.carrier := ⟨t, htS.1⟩
  refine ⟨⟨tL, ?_, ?_⟩⟩
  · intro hzero
    apply htS.2.1
    exact congrArg Subtype.val hzero
  · intro s hs
    by_cases hsu : ‖(s : Plane)‖ ≤ ‖(u : Plane)‖
    · exact htmin (s : Plane) ⟨s.property, by exact_mod_cast hs, hsu⟩
    · exact htS.2.2.trans (lt_of_not_ge hsu).le

/-- A shortest vector and its image are real-linearly independent in the three elliptic cases. -/
theorem shortest_orbit_real_linearIndependent
    (L : RankTwoLattice Plane)
    (A : L.carrier ≃ₗ[ℤ] L.carrier)
    (φ : Plane ≃ₗᵢ[ℝ] Plane)
    (hA : ∀ x : L.carrier, (A x : Plane) = φ (x : Plane))
    (t : ShortestVector L) (c : ℝ)
    (hc : c = -1 ∨ c = 0 ∨ c = 1)
    (hinner : ⟪(t.vector : Plane), φ (t.vector : Plane)⟫_ℝ =
      c / 2 * ‖(t.vector : Plane)‖ ^ 2) :
    LinearIndependent ℝ ![(t.vector : Plane), (A t.vector : Plane)] := by
  rw [LinearIndependent.pair_iff' (by exact_mod_cast t.ne_zero)]
  intro a ha
  have htpos : 0 < ‖(t.vector : Plane)‖ := norm_pos_iff.mpr (by exact_mod_cast t.ne_zero)
  have hnorm : |a| * ‖(t.vector : Plane)‖ = ‖(t.vector : Plane)‖ := by
    calc
      |a| * ‖(t.vector : Plane)‖ = ‖a • (t.vector : Plane)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = ‖(A t.vector : Plane)‖ := congrArg norm ha
      _ = ‖φ (t.vector : Plane)‖ := by rw [hA]
      _ = ‖(t.vector : Plane)‖ := φ.norm_map _
  have habs : |a| = 1 := by nlinarith
  have hi := congrArg (fun x : Plane => ⟪(t.vector : Plane), x⟫_ℝ) ha
  have haeq : a * ‖(t.vector : Plane)‖ ^ 2 =
      c / 2 * ‖(t.vector : Plane)‖ ^ 2 := by
    calc
      a * ‖(t.vector : Plane)‖ ^ 2 =
          ⟪(t.vector : Plane), a • (t.vector : Plane)⟫_ℝ := by
            rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      _ = ⟪(t.vector : Plane), (A t.vector : Plane)⟫_ℝ := hi
      _ = ⟪(t.vector : Plane), φ (t.vector : Plane)⟫_ℝ := by rw [hA]
      _ = c / 2 * ‖(t.vector : Plane)‖ ^ 2 := hinner
  have hsqpos : 0 < ‖(t.vector : Plane)‖ ^ 2 := sq_pos_of_pos htpos
  rcases hc with rfl | rfl | rfl
  · have ha' : a = (-1 / 2 : ℝ) := by nlinarith
    rw [ha'] at habs
    norm_num at habs
  · have ha' : a = 0 := by nlinarith
    rw [ha'] at habs
    norm_num at habs
  · have ha' : a = (1 / 2 : ℝ) := by nlinarith
    rw [ha'] at habs
    norm_num at habs

/--
The integral basis `(t, A t)` obtained from a shortest vector by nearest-integer reduction.

The coefficient `c` is the trace of the determinant-one isometry.  The uniform estimate for
`c = -1, 0, 1` bounds every centered coordinate remainder by three quarters of `‖t‖²`, so
minimality forces the remainder to vanish.
-/
noncomputable def shortestOrbitBasis
    (L : RankTwoLattice Plane)
    (A : L.carrier ≃ₗ[ℤ] L.carrier)
    (φ : Plane ≃ₗᵢ[ℝ] Plane)
    (hA : ∀ x : L.carrier, (A x : Plane) = φ (x : Plane))
    (t : ShortestVector L) (c : ℝ)
    (hc : c = -1 ∨ c = 0 ∨ c = 1)
    (hinner : ⟪(t.vector : Plane), φ (t.vector : Plane)⟫_ℝ =
      c / 2 * ‖(t.vector : Plane)‖ ^ 2) :
    Module.Basis (Fin 2) ℤ L.carrier := by
  let vZ : Fin 2 → L.carrier := ![t.vector, A t.vector]
  let vR : Fin 2 → Plane := ![(t.vector : Plane), (A t.vector : Plane)]
  have hliR : LinearIndependent ℝ vR := by
    exact shortest_orbit_real_linearIndependent L A φ hA t c hc hinner
  have hliZambient : LinearIndependent ℤ vR := hliR.restrict_scalars' ℤ
  have hliZ : LinearIndependent ℤ vZ := by
    apply LinearIndependent.of_comp L.carrier.subtype
    convert hliZambient using 1
    funext i
    fin_cases i <;> rfl
  apply Module.Basis.mk hliZ
  intro x hx
  let bR : Module.Basis (Fin 2) ℝ Plane :=
    basisOfLinearIndependentOfCardEqFinrank hliR (by simp)
  have hb0 : bR 0 = (t.vector : Plane) := by simp [bR, vR]
  have hb1 : bR 1 = (A t.vector : Plane) := by simp [bR, vR]
  let a : ℝ := bR.repr (x : Plane) 0
  let b : ℝ := bR.repr (x : Plane) 1
  let m : ℤ := round a
  let n : ℤ := round b
  let w : L.carrier := x - m • t.vector - n • A t.vector
  have hwa : bR.repr (w : Plane) 0 = a - m := by
    rw [show (w : Plane) =
      (x : Plane) - m • (t.vector : Plane) - n • (A t.vector : Plane) by rfl]
    rw [← hb0, ← hb1]
    simp [a]
  have hwb : bR.repr (w : Plane) 1 = b - n := by
    rw [show (w : Plane) =
      (x : Plane) - m • (t.vector : Plane) - n • (A t.vector : Plane) by rfl]
    rw [← hb0, ← hb1]
    simp [b]
  have haabs : |a - m| ≤ (1 : ℝ) / 2 := abs_sub_round a
  have hbabs : |b - n| ≤ (1 : ℝ) / 2 := abs_sub_round b
  have hwexp : (w : Plane) =
      (a - m) • (t.vector : Plane) + (b - n) • (A t.vector : Plane) := by
    calc
      (w : Plane) = ∑ i, bR.repr (w : Plane) i • bR i := (bR.sum_repr _).symm
      _ = (a - m) • (t.vector : Plane) +
          (b - n) • (A t.vector : Plane) := by
            rw [Fin.sum_univ_two, hwa, hwb, hb0, hb1]
  have hnormA : ‖(A t.vector : Plane)‖ = ‖(t.vector : Plane)‖ := by
    rw [hA]
    exact φ.norm_map _
  have hinnerA : ⟪(t.vector : Plane), (A t.vector : Plane)⟫_ℝ =
      c / 2 * ‖(t.vector : Plane)‖ ^ 2 := by
    rw [hA]
    exact hinner
  have hwnormsq : ‖(w : Plane)‖ ^ 2 =
      ((a - m) ^ 2 + (b - n) ^ 2 + c * (a - m) * (b - n)) *
        ‖(t.vector : Plane)‖ ^ 2 := by
    rw [hwexp, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left,
      real_inner_smul_right, hinnerA, hnormA]
    simp only [mul_pow, sq_abs]
    ring
  have hquad :
      (a - m) ^ 2 + (b - n) ^ 2 + c * (a - m) * (b - n) ≤ (3 : ℝ) / 4 := by
    have ha := (abs_le.mp haabs)
    have hb := (abs_le.mp hbabs)
    have haa : (a - m) ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith
    have hbb : (b - n) ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith
    rcases hc with rfl | rfl | rfl
    · nlinarith [sq_nonneg ((a - m) + (b - n))]
    · nlinarith
    · nlinarith [sq_nonneg ((a - m) - (b - n))]
  have htpos : 0 < ‖(t.vector : Plane)‖ :=
    norm_pos_iff.mpr (by exact_mod_cast t.ne_zero)
  have hwnormlt : ‖(w : Plane)‖ < ‖(t.vector : Plane)‖ := by
    have hsq : ‖(w : Plane)‖ ^ 2 ≤
        (3 / 4 : ℝ) * ‖(t.vector : Plane)‖ ^ 2 := by
      rw [hwnormsq]
      exact mul_le_mul_of_nonneg_right hquad (sq_nonneg _)
    by_contra hn
    have hle : ‖(t.vector : Plane)‖ ≤ ‖(w : Plane)‖ := le_of_not_gt hn
    have hsquare := mul_self_le_mul_self (norm_nonneg _) hle
    nlinarith [sq_nonneg ‖(t.vector : Plane)‖]
  have hwzero : w = 0 := by
    by_contra hw
    exact (not_lt_of_ge (t.minimal w hw)) hwnormlt
  have hxeq : x = m • t.vector + n • A t.vector := by
    dsimp [w] at hwzero
    have h1 : x - m • t.vector = n • A t.vector := sub_eq_zero.mp hwzero
    calc
      x = (x - m • t.vector) + m • t.vector := by abel
      _ = n • A t.vector + m • t.vector := by rw [h1]
      _ = m • t.vector + n • A t.vector := add_comm _ _
  rw [hxeq]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 0))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 1))

end RankTwoLattice

/-- The standard integral rotation matrix with trace `c`. -/
def rotationMatrix (c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, c]

/-- Standard order-three lattice rotation matrix. -/
def rotationMatrix3 : Matrix (Fin 2) (Fin 2) ℤ := rotationMatrix (-1)
/-- Standard order-four lattice rotation matrix. -/
def rotationMatrix4 : Matrix (Fin 2) (Fin 2) ℤ := rotationMatrix 0
/-- Standard order-six lattice rotation matrix. -/
def rotationMatrix6 : Matrix (Fin 2) (Fin 2) ℤ := rotationMatrix 1

/-- Cayley–Hamilton for a real endomorphism of the plane in trace-determinant form. -/
lemma plane_endomorphism_cayley_hamilton (T : Plane →ₗ[ℝ] Plane) :
    T * T - (LinearMap.trace ℝ Plane T) • T +
      (LinearMap.det T) • (1 : Plane →ₗ[ℝ] Plane) = 0 := by
  let b := Plane.canonicalRealBasis
  apply (LinearMap.toMatrix b b).injective
  have h := Matrix.aeval_self_charpoly (LinearMap.toMatrix b b T)
  rw [Matrix.charpoly_fin_two] at h
  have h' :
      (LinearMap.toMatrix b b T) ^ 2 -
        (LinearMap.toMatrix b b T).trace • (LinearMap.toMatrix b b T) +
        (LinearMap.toMatrix b b T).det •
          (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    simpa [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, Algebra.smul_def, smul_eq_mul] using h
  rw [← LinearMap.trace_eq_matrix_trace ℝ b T] at h'
  rw [LinearMap.det_toMatrix b T] at h'
  simpa [pow_two, map_add, map_sub, LinearMap.toMatrix_mul, map_smul] using h'

/-- A determinant-one plane isometry satisfies `⟪x, φ x⟫ = trace(φ) / 2 ⋅ ‖x‖²`. -/
lemma linearIsometry_inner_map_eq_trace_half
    (φ : Plane ≃ₗᵢ[ℝ] Plane)
    (hdet : LinearMap.det φ.toLinearEquiv.toLinearMap = 1)
    (x : Plane) :
    ⟪x, φ x⟫_ℝ =
      LinearMap.trace ℝ Plane φ.toLinearEquiv.toLinearMap / 2 * ‖x‖ ^ 2 := by
  let T := φ.toLinearEquiv.toLinearMap
  have hch := plane_endomorphism_cayley_hamilton T
  have hx := LinearMap.congr_fun hch x
  have hx' : φ (φ x) - LinearMap.trace ℝ Plane T • φ x + x = 0 := by
    simpa [T, Module.End.mul_apply, hdet] using hx
  have hin := congrArg (fun y : Plane => ⟪φ x, y⟫_ℝ) hx'
  have hpres : ⟪φ x, φ (φ x)⟫_ℝ = ⟪x, φ x⟫_ℝ := by
    exact φ.inner_map_map x (φ x)
  rw [inner_zero_right] at hin
  change ⟪φ x, φ (φ x) -
      LinearMap.trace ℝ Plane T • φ x + x⟫_ℝ = 0 at hin
  rw [inner_add_right, inner_sub_right, hpres, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm (φ x) x] at hin
  rw [φ.norm_map] at hin
  have hsym : ⟪φ x, x⟫_ℝ = ⟪x, φ x⟫_ℝ := real_inner_comm _ _
  rw [hsym] at hin
  linarith

/-- Every integer basis of a rank-two plane lattice remains linearly independent over `ℝ`. -/
lemma RankTwoLattice.anyBasis_real_linearIndependent
    (L : RankTwoLattice Plane) (b : Module.Basis (Fin 2) ℤ L.carrier) :
    LinearIndependent ℝ (fun i => (b i : Plane)) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [← L.realBasis.span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    rw [L.realBasis_apply]
    have h : ∑ j, (b.repr (L.basis i)) j • (b j : Plane) =
        (L.basis i : Plane) := by
      simpa only [map_sum, map_zsmul, Submodule.coe_subtype] using
        congrArg L.carrier.subtype (b.sum_repr (L.basis i))
    rw [← h]
    apply Submodule.sum_mem
    intro j hj
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · simp

namespace PlaneGroup

/-- A shortest orbit vector together with an integral basis and its action matrix. -/
structure LatticeActionNormalForm (G : PlaneGroup) (h : pointGroup G.carrier)
    (M : Matrix (Fin 2) (Fin 2) ℤ) where
  /-- A shortest nonzero vector in the translation lattice. -/
  shortest : G.translationLattice.ShortestVector
  /-- The integral orbit basis. -/
  basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier
  /-- The first basis vector is the shortest vector. -/
  basis_zero : basis 0 = shortest.vector
  /-- The second basis vector is the image of the first. -/
  basis_one : basis 1 = G.latticeAction h shortest.vector
  /-- The lattice action has the requested matrix in the orbit basis. -/
  matrix_eq : LinearMap.toMatrix basis basis (G.latticeAction h).toLinearMap = M

/-- A positive lattice action of trace `-1`, `0`, or `1` has the corresponding orbit normal form. -/
theorem exists_latticeActionNormalForm_of_trace
    (G : PlaneGroup) (h : orientationPreservingPointGroup G) (c : ℤ)
    (hc : c = -1 ∨ c = 0 ∨ c = 1)
    (htrace : (G.latticeActionMatrix h.1).trace = c) :
    Nonempty (LatticeActionNormalForm G h.1 (rotationMatrix c)) := by
  let L := G.translationLattice
  let A := G.latticeAction h.1
  let φ : Plane ≃ₗᵢ[ℝ] Plane := (h.1 : Plane ≃ₗᵢ[ℝ] Plane)
  obtain ⟨t⟩ := L.exists_shortestVector
  have hdet : LinearMap.det φ.toLinearEquiv.toLinearMap = 1 :=
    positive_isometry_det_eq_one φ (orientationPreserving_det_pos G h)
  have hinner : ⟪(t.vector : Plane), φ (t.vector : Plane)⟫_ℝ =
      (c : ℝ) / 2 * ‖(t.vector : Plane)‖ ^ 2 := by
    rw [linearIsometry_inner_map_eq_trace_half φ hdet]
    rw [← G.trace_cast h.1]
    rw [htrace]
  have hcR : (c : ℝ) = -1 ∨ (c : ℝ) = 0 ∨ (c : ℝ) = 1 := by
    rcases hc with rfl | rfl | rfl <;> norm_num
  let b := L.shortestOrbitBasis A φ (G.latticeAction_coe h.1) t (c : ℝ) hcR hinner
  have hb0 : b 0 = t.vector := by simp [b, RankTwoLattice.shortestOrbitBasis]
  have hb1 : b 1 = A t.vector := by simp [b, RankTwoLattice.shortestOrbitBasis]
  let N := LinearMap.toMatrix b b A.toLinearMap
  have htraceN : N.trace = c := by
    calc
      N.trace = LinearMap.trace ℤ L.carrier A.toLinearMap :=
        (LinearMap.trace_eq_matrix_trace ℤ b A.toLinearMap).symm
      _ = (L.equivMatrix L A).trace := by
        simpa [RankTwoLattice.equivMatrix] using
          LinearMap.trace_eq_matrix_trace ℤ L.basis A.toLinearMap
      _ = c := by
        simpa [L, A, latticeActionMatrix] using htrace
  have hdetOld : (G.latticeActionMatrix h.1).det = 1 :=
    G.integral_det_eq_one h.1 (orientationPreserving_det_pos G h)
  have hdetN : N.det = 1 := by
    calc
      N.det = LinearMap.det A.toLinearMap :=
        LinearMap.det_toMatrix b A.toLinearMap
      _ = (L.equivMatrix L A).det := by
        simp [RankTwoLattice.equivMatrix]
      _ = 1 := by
        simpa [L, A, latticeActionMatrix] using hdetOld
  have h00 : N 0 0 = 0 := by
    dsimp [N]
    rw [LinearMap.toMatrix_apply]
    change b.repr (A (b 0)) 0 = 0
    rw [hb0, ← hb1]
    simp
  have h10 : N 1 0 = 1 := by
    dsimp [N]
    rw [LinearMap.toMatrix_apply]
    change b.repr (A (b 0)) 1 = 1
    rw [hb0, ← hb1]
    simp
  have h11 : N 1 1 = c := by
    rw [Matrix.trace_fin_two, h00, zero_add] at htraceN
    exact htraceN
  have h01 : N 0 1 = -1 := by
    rw [Matrix.det_fin_two, h00, h10, h11] at hdetN
    omega
  refine ⟨⟨t, b, hb0, hb1, ?_⟩⟩
  change N = rotationMatrix c
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rotationMatrix] using h00
  · simpa [rotationMatrix] using h01
  · simpa [rotationMatrix] using h10
  · simpa [rotationMatrix] using h11

/-- An orientation-preserving element of order three has the standard shortest-orbit basis. -/
theorem exists_orderThree_latticeActionNormalForm
    (G : PlaneGroup) (h : orientationPreservingPointGroup G)
    (horder : orderOf h.1 = 3) :
    Nonempty (LatticeActionNormalForm G h.1 rotationMatrix3) := by
  simpa [rotationMatrix3] using
    exists_latticeActionNormalForm_of_trace G h (-1) (Or.inl rfl)
      (G.orientationPreserving_trace_eq_of_order_three h horder)

/-- An orientation-preserving element of order four has the standard shortest-orbit basis. -/
theorem exists_orderFour_latticeActionNormalForm
    (G : PlaneGroup) (h : orientationPreservingPointGroup G)
    (horder : orderOf h.1 = 4) :
    Nonempty (LatticeActionNormalForm G h.1 rotationMatrix4) := by
  simpa [rotationMatrix4] using
    exists_latticeActionNormalForm_of_trace G h 0 (Or.inr (Or.inl rfl))
      (G.orientationPreserving_trace_eq_of_order_four h horder)

/-- An orientation-preserving element of order six has the standard shortest-orbit basis. -/
theorem exists_orderSix_latticeActionNormalForm
    (G : PlaneGroup) (h : orientationPreservingPointGroup G)
    (horder : orderOf h.1 = 6) :
    Nonempty (LatticeActionNormalForm G h.1 rotationMatrix6) := by
  simpa [rotationMatrix6] using
    exists_latticeActionNormalForm_of_trace G h 1 (Or.inr (Or.inr rfl))
      (G.orientationPreserving_trace_eq_of_order_six h horder)

end PlaneGroup

end

end WallpaperGroups
