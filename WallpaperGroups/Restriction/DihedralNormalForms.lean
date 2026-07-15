import WallpaperGroups.Invariants.ReflectionFamilies
import WallpaperGroups.Restriction.ReflectionNormalForms

set_option linter.style.header false

/-!
# Joint integral normal forms for dihedral point actions

This file chooses adjacent reflection generators for a point group with more than one
reflection and classifies their simultaneous action on the translation lattice.  A single
reflection normal form is not sufficient in order three: both order-three forms have centered
individual reflections, but their reflection axes generate sublattices of indices one and three.
-/

set_option autoImplicit false

namespace WallpaperGroups

open Matrix
open EuclideanMotion

noncomputable section

/-- The four possible nontrivial rotation orders in a dihedral plane point group. -/
inductive DihedralRotationOrder where
  | two
  | three
  | four
  | six
  deriving DecidableEq, Fintype

namespace DihedralRotationOrder

/-- Natural-number value of a nontrivial crystallographic rotation order. -/
def toNat : DihedralRotationOrder → ℕ
  | .two => 2
  | .three => 3
  | .four => 4
  | .six => 6

end DihedralRotationOrder

/-- Adjacent-generator data for a dihedral plane point group. -/
structure DihedralGenerators (G : PlaneGroup) where
  /-- A generator of the orientation-preserving point subgroup. -/
  rotation : orientationPreservingPointGroup G
  /-- A selected orientation-reversing point element. -/
  reflection : pointGroup G.carrier
  /-- The selected reflection reverses orientation. -/
  reflection_reversing : reflection ∉ orientationPreservingPointGroup G
  /-- Every positive point element is a power of the selected rotation. -/
  rotation_generates : ∀ r : orientationPreservingPointGroup G,
    r ∈ Subgroup.zpowers rotation
  /-- The rotation generator is nontrivial. -/
  rotation_ne_one : rotation ≠ 1
  /-- Its typed crystallographic order. -/
  order : DihedralRotationOrder
  /-- The selected rotation has the advertised exact order. -/
  rotation_order : orderOf rotation.1 = order.toNat

namespace DihedralGenerators

variable {G : PlaneGroup}

/-- Adjacent dihedral generator data immediately witnesses that the point group has more than
one reflection. -/
theorem pointGroupHasMultipleReflections (d : DihedralGenerators G) :
    PointGroupHasMultipleReflections G :=
  ⟨⟨d.reflection, d.reflection_reversing⟩, ⟨d.rotation, d.rotation_ne_one⟩⟩

/-- The adjacent second reflection, chosen so that `reflection * secondReflection = rotation`. -/
def secondReflection (d : DihedralGenerators G) : pointGroup G.carrier :=
  d.reflection * d.rotation.1

/-- The first selected reflection is an involution. -/
theorem reflection_sq (d : DihedralGenerators G) : d.reflection ^ 2 = 1 :=
  pointGroup_reversing_sq G d.reflection d.reflection_reversing

/-- The adjacent second generator also reverses orientation. -/
theorem secondReflection_reversing (d : DihedralGenerators G) :
    d.secondReflection ∉ orientationPreservingPointGroup G := by
  intro hsecond
  apply d.reflection_reversing
  have hrinv : (d.rotation.1 : pointGroup G.carrier)⁻¹ ∈
      orientationPreservingPointGroup G :=
    (orientationPreservingPointGroup G).inv_mem d.rotation.2
  have hmul := (orientationPreservingPointGroup G).mul_mem hsecond hrinv
  simpa [secondReflection, mul_assoc] using hmul

/-- The second selected reflection is an involution. -/
theorem secondReflection_sq (d : DihedralGenerators G) :
    d.secondReflection ^ 2 = 1 :=
  pointGroup_reversing_sq G d.secondReflection d.secondReflection_reversing

/-- The product of the adjacent reflections is the selected positive generator. -/
theorem reflection_mul_secondReflection (d : DihedralGenerators G) :
    d.reflection * d.secondReflection = d.rotation.1 := by
  rw [secondReflection, ← mul_assoc]
  rw [show d.reflection * d.reflection = 1 by simpa [pow_two] using d.reflection_sq]
  simp

/-- The selected reversing generator conjugates the positive generator to its inverse. -/
theorem reflection_conjugates_rotation (d : DihedralGenerators G) :
    d.reflection * d.rotation.1 * d.reflection⁻¹ = (d.rotation.1)⁻¹ :=
  pointGroup_reversing_conjugates_to_inverse G d.reflection
    d.reflection_reversing d.rotation

/-- Commuting a reflection past the positive generator inverts the generator. -/
theorem reflection_mul_rotation (d : DihedralGenerators G) :
    d.reflection * d.rotation.1 = (d.rotation.1)⁻¹ * d.reflection := by
  calc
    d.reflection * d.rotation.1 =
        (d.reflection * d.rotation.1 * d.reflection⁻¹) * d.reflection := by
      group
    _ = (d.rotation.1)⁻¹ * d.reflection := by
      rw [d.reflection_conjugates_rotation]

/-- Replace the selected reflection by another reflection in the same reversing coset. -/
def rotateReflection (d : DihedralGenerators G) (n : ℕ) : DihedralGenerators G where
  rotation := d.rotation
  reflection := d.reflection * d.rotation.1 ^ n
  reflection_reversing := by
    intro h
    apply d.reflection_reversing
    have hp : d.rotation.1 ^ n ∈ orientationPreservingPointGroup G := by
      exact (d.rotation ^ n).2
    have hpinv := (orientationPreservingPointGroup G).inv_mem hp
    have hm := (orientationPreservingPointGroup G).mul_mem h hpinv
    simpa [mul_assoc] using hm
  rotation_generates := d.rotation_generates
  rotation_ne_one := d.rotation_ne_one
  order := d.order
  rotation_order := d.rotation_order

@[simp]
theorem rotateReflection_rotation (d : DihedralGenerators G) (n : ℕ) :
    (d.rotateReflection n).rotation = d.rotation :=
  rfl

@[simp]
theorem rotateReflection_reflection (d : DihedralGenerators G) (n : ℕ) :
    (d.rotateReflection n).reflection = d.reflection * d.rotation.1 ^ n :=
  rfl

/-- Rotating the selected reflection once makes the old adjacent reflection the new first
reflection. -/
@[simp]
theorem rotateReflection_one_reflection (d : DihedralGenerators G) :
    (d.rotateReflection 1).reflection = d.secondReflection := by
  simp [secondReflection]

/-- Every point element is a rotation or the selected reflection times a rotation. -/
theorem point_two_coset_normal_form (d : DihedralGenerators G)
    (g : pointGroup G.carrier) :
    (∃ r : orientationPreservingPointGroup G,
        r ∈ Subgroup.zpowers d.rotation ∧ g = r.1) ∨
      ∃ r : orientationPreservingPointGroup G,
        r ∈ Subgroup.zpowers d.rotation ∧ g = d.reflection * r.1 := by
  rcases pointGroup_rotation_or_reflection_mul G d.reflection
      d.reflection_reversing g with hg | ⟨r, hr⟩
  · exact Or.inl ⟨⟨g, hg⟩, d.rotation_generates ⟨g, hg⟩, rfl⟩
  · exact Or.inr ⟨r, d.rotation_generates r, hr⟩

/-- Under a translation-preserving isomorphism, the selected positive generator maps to an
integer power of any selected positive generator on the target. -/
theorem pointGroupEquiv_rotation_eq_zpow
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (dG : DihedralGenerators G) (dH : DihedralGenerators H) :
    ∃ k : ℤ, e.pointGroupEquiv dG.rotation.1 = dH.rotation.1 ^ k := by
  let rH : orientationPreservingPointGroup H :=
    ⟨e.pointGroupEquiv dG.rotation.1,
      (e.pointGroupEquiv_mem_orientationPreserving_iff dG.rotation.1).2
        dG.rotation.2⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (dH.rotation_generates rH)
  refine ⟨k, ?_⟩
  have hkval := congrArg Subtype.val hk
  simpa [rH] using hkval.symm

/-- Under a translation-preserving isomorphism, a selected reversing generator maps into the
reversing coset of any selected target reflection, with a `zpowers` witness. -/
theorem pointGroupEquiv_reflection_eq_mul_zpow
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (dG : DihedralGenerators G) (dH : DihedralGenerators H) :
    ∃ k : ℤ,
      e.pointGroupEquiv dG.reflection = dH.reflection * dH.rotation.1 ^ k := by
  have hsH : e.pointGroupEquiv dG.reflection ∉
      orientationPreservingPointGroup H := by
    intro hs
    exact dG.reflection_reversing
      ((e.pointGroupEquiv_mem_orientationPreserving_iff dG.reflection).1 hs)
  rcases dH.point_two_coset_normal_form (e.pointGroupEquiv dG.reflection) with
    ⟨r, -, hr⟩ | ⟨r, hrpow, hr⟩
  · exfalso
    apply hsH
    rw [hr]
    exact r.2
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hrpow
    have hkval : dH.rotation.1 ^ k = r.1 := by
      simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    calc
      e.pointGroupEquiv dG.reflection = dH.reflection * r.1 := hr
      _ = dH.reflection * dH.rotation.1 ^ k := by rw [hkval]

/-- Combined generator-coset bridge used by equivalence and uniqueness arguments. -/
theorem pointGroupEquiv_generators_zpower_normal_form
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (dG : DihedralGenerators G) (dH : DihedralGenerators H) :
    (∃ k : ℤ, e.pointGroupEquiv dG.rotation.1 = dH.rotation.1 ^ k) ∧
      ∃ k : ℤ,
        e.pointGroupEquiv dG.reflection = dH.reflection * dH.rotation.1 ^ k :=
  ⟨pointGroupEquiv_rotation_eq_zpow e dG dH,
    pointGroupEquiv_reflection_eq_mul_zpow e dG dH⟩

/-- Alias emphasizing that positive powers are exhaustive. -/
theorem rotation_powers_exhaustive (d : DihedralGenerators G) :
    ∀ r : orientationPreservingPointGroup G, r ∈ Subgroup.zpowers d.rotation :=
  d.rotation_generates

/-- Alias used by the classification layer for the nontriviality field. -/
theorem rotationGenerator_ne_one (d : DihedralGenerators G) : d.rotation ≠ 1 :=
  d.rotation_ne_one

end DihedralGenerators

/-- Every point group with two distinct reflections admits adjacent generators of rotation
order `2`, `3`, `4`, or `6`. -/
theorem exists_dihedralGenerators (G : PlaneGroup)
    (hG : PointGroupHasMultipleReflections G) :
    Nonempty (DihedralGenerators G) := by
  classical
  obtain ⟨⟨s, hs⟩, ⟨r, hrne⟩⟩ := hG
  letI : IsCyclic (orientationPreservingPointGroup G) :=
    orientationPreserving_isCyclic G
  obtain ⟨rho, hrho⟩ := IsCyclic.exists_generator
    (α := orientationPreservingPointGroup G)
  have rhone : rho ≠ 1 := by
    intro h1
    have hm := hrho r
    simp [h1] at hm
    exact hrne (by simpa using hm)
  have hcases := G.orientationPreserving_point_order_cases rho
  rcases hcases with h1 | h2 | h3 | h4 | h6
  · exact (rhone (Subtype.ext (orderOf_eq_one_iff.mp h1))).elim
  · exact ⟨⟨rho, s, hs, hrho, rhone, .two, by
      simpa [DihedralRotationOrder.toNat] using h2⟩⟩
  · exact ⟨⟨rho, s, hs, hrho, rhone, .three, by
      simpa [DihedralRotationOrder.toNat] using h3⟩⟩
  · exact ⟨⟨rho, s, hs, hrho, rhone, .four, by
      simpa [DihedralRotationOrder.toNat] using h4⟩⟩
  · exact ⟨⟨rho, s, hs, hrho, rhone, .six, by
      simpa [DihedralRotationOrder.toNat] using h6⟩⟩

/-! ## Explicit simultaneous matrices -/

/-- The standard half-turn matrix. -/
def dihedralRotationMatrix2 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, -1]

/-- The order-three reflection whose primitive fixed axes span the entire lattice. -/
def dihedralReflectionMatrix3Full : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, -1]

/-- The other order-three reflection embedding; its primitive fixed axes span an index-three
sublattice. -/
def dihedralReflectionMatrix3IndexThree : Matrix (Fin 2) (Fin 2) ℤ :=
  -dihedralReflectionMatrix3Full

/-- The normalized order-four first reflection. -/
def dihedralReflectionMatrix4 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- The normalized order-six first reflection. -/
def dihedralReflectionMatrix6 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, -1]

/-- The inverse of the companion rotation matrix `!![0,-1;1,c]`. -/
def dihedralRotationInverseMatrix (c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![c, 1; -1, 0]

@[simp]
lemma rotationMatrix_mul_dihedralRotationInverseMatrix (c : ℤ) :
    rotationMatrix c * dihedralRotationInverseMatrix c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, dihedralRotationInverseMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp]
lemma dihedralRotationInverseMatrix_mul_rotationMatrix (c : ℤ) :
    dihedralRotationInverseMatrix c * rotationMatrix c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, dihedralRotationInverseMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- An integer matrix reversing the companion rotation has the displayed two-parameter shape. -/
lemma matrix_eq_of_mul_rotationMatrix_eq_inverse_mul
    (B : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ)
    (h : B * rotationMatrix c = dihedralRotationInverseMatrix c * B) :
    B = !![B 0 0, B 0 1; B 0 1 - c * B 0 0, -B 0 0] := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  simp [rotationMatrix, dihedralRotationInverseMatrix, Matrix.mul_apply,
    Fin.sum_univ_two] at h00 h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all <;> ring_nf at * <;> omega

/-- Determinant `-1` reduces the shaped reflection matrix to a positive-definite norm equation. -/
lemma reflection_norm_equation
    (B : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ)
    (hshape : B = !![B 0 0, B 0 1; B 0 1 - c * B 0 0, -B 0 0])
    (hdet : B.det = -1) :
    B 0 0 ^ 2 + B 0 1 ^ 2 - c * B 0 0 * B 0 1 = 1 := by
  rw [hshape] at hdet
  simp [Matrix.det_fin_two] at hdet
  ring_nf at hdet ⊢
  nlinarith

/-- The six unit vectors of the Eisenstein norm split into the two order-three reflection
orbits. -/
lemma orderThree_shape_normalization (a b : ℤ)
    (h : a ^ 2 + b ^ 2 + a * b = 1) :
    (∃ n : Fin 3,
        !![a, b; b + a, -a] * rotationMatrix3 ^ n.val =
          dihedralReflectionMatrix3Full) ∨
      ∃ n : Fin 3,
        !![a, b; b + a, -a] * rotationMatrix3 ^ n.val =
          dihedralReflectionMatrix3IndexThree := by
  have haU : a < 2 := by
    by_contra hn
    have ha : 2 ≤ a := by omega
    nlinarith [sq_nonneg b, sq_nonneg (a + b)]
  have haL : -2 < a := by
    by_contra hn
    have ha : a ≤ -2 := by omega
    nlinarith [sq_nonneg b, sq_nonneg (a + b)]
  have hbU : b < 2 := by
    by_contra hn
    have hb : 2 ≤ b := by omega
    nlinarith [sq_nonneg a, sq_nonneg (a + b)]
  have hbL : -2 < b := by
    by_contra hn
    have hb : b ≤ -2 := by omega
    nlinarith [sq_nonneg a, sq_nonneg (a + b)]
  interval_cases a <;> interval_cases b
  all_goals norm_num at h
  all_goals decide

/-- The four Gaussian unit vectors form one order-four reflection orbit. -/
lemma orderFour_shape_normalization (a b : ℤ)
    (h : a ^ 2 + b ^ 2 = 1) :
    ∃ n : Fin 4,
      !![a, b; b, -a] * rotationMatrix4 ^ n.val =
        dihedralReflectionMatrix4 := by
  have haU : a < 2 := by nlinarith [sq_nonneg b]
  have haL : -2 < a := by nlinarith [sq_nonneg b]
  have hbU : b < 2 := by nlinarith [sq_nonneg a]
  have hbL : -2 < b := by nlinarith [sq_nonneg a]
  interval_cases a <;> interval_cases b
  all_goals norm_num at h
  all_goals decide

/-- The six units of the conjugate Eisenstein norm form one order-six reflection orbit. -/
lemma orderSix_shape_normalization (a b : ℤ)
    (h : a ^ 2 + b ^ 2 - a * b = 1) :
    ∃ n : Fin 6,
      !![a, b; b - a, -a] * rotationMatrix6 ^ n.val =
        dihedralReflectionMatrix6 := by
  have haU : a < 2 := by
    by_contra hn
    have ha : 2 ≤ a := by omega
    nlinarith [sq_nonneg b, sq_nonneg (a - b)]
  have haL : -2 < a := by
    by_contra hn
    have ha : a ≤ -2 := by omega
    nlinarith [sq_nonneg b, sq_nonneg (a - b)]
  have hbU : b < 2 := by
    by_contra hn
    have hb : 2 ≤ b := by omega
    nlinarith [sq_nonneg a, sq_nonneg (a - b)]
  have hbL : -2 < b := by
    by_contra hn
    have hb : b ≤ -2 := by omega
    nlinarith [sq_nonneg a, sq_nonneg (a - b)]
  interval_cases a <;> interval_cases b
  all_goals norm_num at h
  all_goals decide

/-! ## The six joint forms -/

/-- The six possible simultaneous integral lattice-action forms before shift data are added. -/
inductive DihedralLatticeForm where
  | orderTwoPrimitive
  | orderTwoCentered
  /-- The order-three form whose reflection axes span the full lattice (`p3m1`). -/
  | p3m1
  /-- The order-three form whose reflection axes span an index-three lattice (`p31m`). -/
  | p31m
  | orderFour
  | orderSix
  deriving DecidableEq

namespace DihedralLatticeForm

/-- Rotation order associated to a simultaneous lattice form. -/
def order : DihedralLatticeForm → DihedralRotationOrder
  | .orderTwoPrimitive | .orderTwoCentered => .two
  | .p3m1 | .p31m => .three
  | .orderFour => .four
  | .orderSix => .six

/-- Rotation matrix associated to a simultaneous lattice form. -/
def rotationMatrix : DihedralLatticeForm → Matrix (Fin 2) (Fin 2) ℤ
  | .orderTwoPrimitive | .orderTwoCentered => dihedralRotationMatrix2
  | .p3m1 | .p31m => WallpaperGroups.rotationMatrix3
  | .orderFour => WallpaperGroups.rotationMatrix4
  | .orderSix => WallpaperGroups.rotationMatrix6

/-- First-reflection matrix associated to a simultaneous lattice form. -/
def reflectionMatrix : DihedralLatticeForm → Matrix (Fin 2) (Fin 2) ℤ
  | .orderTwoPrimitive => IntegralReflection.reflectionLatticeMatrix .primitive
  | .orderTwoCentered => IntegralReflection.reflectionLatticeMatrix .centered
  | .p3m1 => dihedralReflectionMatrix3Full
  | .p31m => dihedralReflectionMatrix3IndexThree
  | .orderFour => dihedralReflectionMatrix4
  | .orderSix => dihedralReflectionMatrix6

/-- The adjacent second reflection has matrix `S A`. -/
def secondReflectionMatrix (f : DihedralLatticeForm) : Matrix (Fin 2) (Fin 2) ℤ :=
  f.reflectionMatrix * f.rotationMatrix

/-- Integral reflection kind of the first selected reflection. -/
def firstReflectionKind : DihedralLatticeForm → IntegralReflection.ReflectionLatticeKind
  | .orderTwoPrimitive | .orderFour => .primitive
  | .orderTwoCentered | .p3m1 | .p31m | .orderSix => .centered

/-- Integral reflection kind of the adjacent second reflection. -/
def secondReflectionKind : DihedralLatticeForm → IntegralReflection.ReflectionLatticeKind
  | .orderTwoPrimitive => .primitive
  | .orderTwoCentered | .p3m1 | .p31m | .orderFour | .orderSix => .centered

theorem reflectionKinds_eq_of_order_two (f : DihedralLatticeForm)
    (h : f.order = .two) : f.firstReflectionKind = f.secondReflectionKind := by
  cases f <;> simp [order, firstReflectionKind, secondReflectionKind] at h ⊢

theorem reflectionKinds_centered_of_order_three (f : DihedralLatticeForm)
    (h : f.order = .three) :
    f.firstReflectionKind = .centered ∧ f.secondReflectionKind = .centered := by
  cases f <;> simp [order, firstReflectionKind, secondReflectionKind] at h ⊢

theorem reflectionKinds_of_order_four (f : DihedralLatticeForm)
    (h : f.order = .four) :
    f.firstReflectionKind = .primitive ∧ f.secondReflectionKind = .centered := by
  cases f <;> simp [order, firstReflectionKind, secondReflectionKind] at h ⊢

theorem reflectionKinds_centered_of_order_six (f : DihedralLatticeForm)
    (h : f.order = .six) :
    f.firstReflectionKind = .centered ∧ f.secondReflectionKind = .centered := by
  cases f <;> simp [order, firstReflectionKind, secondReflectionKind] at h ⊢

end DihedralLatticeForm

/-! ## Intrinsic reflection-kind tests for the joint matrices -/

/-- The fixed lattice of an integral reflection is exhausted by its norm map.  In rank two this
is the intrinsic centered-reflection condition. -/
def MatrixReflectionIsCentered (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∀ z : Fin 2 → ℤ, M *ᵥ z = z → ∃ w : Fin 2 → ℤ, w + M *ᵥ w = z

lemma matrixReflectionIsCentered_orderTwoCentered_first :
    MatrixReflectionIsCentered
      (DihedralLatticeForm.orderTwoCentered.reflectionMatrix) := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.reflectionMatrix,
    IntegralReflection.reflectionLatticeMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at hz0 hz1
  refine ⟨![0, z 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.reflectionMatrix,
      IntegralReflection.reflectionLatticeMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> omega

lemma matrixReflectionIsCentered_orderTwoCentered_second :
    MatrixReflectionIsCentered
      DihedralLatticeForm.orderTwoCentered.secondReflectionMatrix := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.secondReflectionMatrix,
    DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
    IntegralReflection.reflectionLatticeMatrix, dihedralRotationMatrix2,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] at hz0 hz1
  refine ⟨![0, -z 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.secondReflectionMatrix,
      DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
      IntegralReflection.reflectionLatticeMatrix, dihedralRotationMatrix2,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] <;> omega

lemma matrixReflectionIsCentered_p3m1_first :
    MatrixReflectionIsCentered DihedralLatticeForm.p3m1.reflectionMatrix := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.reflectionMatrix, dihedralReflectionMatrix3Full,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hz0 hz1
  refine ⟨![0, -z 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.reflectionMatrix, dihedralReflectionMatrix3Full,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> omega

lemma matrixReflectionIsCentered_p3m1_second :
    MatrixReflectionIsCentered DihedralLatticeForm.p3m1.secondReflectionMatrix := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.secondReflectionMatrix,
    DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
    dihedralReflectionMatrix3Full, rotationMatrix3, rotationMatrix,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] at hz0 hz1
  refine ⟨![-z 1, 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.secondReflectionMatrix,
      DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
      dihedralReflectionMatrix3Full, rotationMatrix3, rotationMatrix,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] <;> omega

lemma matrixReflectionIsCentered_p31m_first :
    MatrixReflectionIsCentered DihedralLatticeForm.p31m.reflectionMatrix := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.reflectionMatrix,
    dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hz0 hz1
  refine ⟨![0, z 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.reflectionMatrix,
      dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> omega

lemma matrixReflectionIsCentered_p31m_second :
    MatrixReflectionIsCentered DihedralLatticeForm.p31m.secondReflectionMatrix := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.secondReflectionMatrix,
    DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
    dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
    rotationMatrix3, rotationMatrix, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_two] at hz0 hz1
  refine ⟨![z 1, 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.secondReflectionMatrix,
      DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
      dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
      rotationMatrix3, rotationMatrix, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_two] <;> omega

lemma matrixReflectionIsCentered_orderFour_second :
    MatrixReflectionIsCentered DihedralLatticeForm.orderFour.secondReflectionMatrix := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.secondReflectionMatrix,
    DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
    dihedralReflectionMatrix4, rotationMatrix4, rotationMatrix,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] at hz0 hz1
  refine ⟨![z 0, 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.secondReflectionMatrix,
      DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
      dihedralReflectionMatrix4, rotationMatrix4, rotationMatrix,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] <;> omega

lemma matrixReflectionIsCentered_orderSix_first :
    MatrixReflectionIsCentered DihedralLatticeForm.orderSix.reflectionMatrix := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.reflectionMatrix, dihedralReflectionMatrix6,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hz0 hz1
  refine ⟨![0, z 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.reflectionMatrix, dihedralReflectionMatrix6,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> omega

lemma matrixReflectionIsCentered_orderSix_second :
    MatrixReflectionIsCentered DihedralLatticeForm.orderSix.secondReflectionMatrix := by
  intro z hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  simp [DihedralLatticeForm.secondReflectionMatrix,
    DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
    dihedralReflectionMatrix6, rotationMatrix6, rotationMatrix,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] at hz0 hz1
  refine ⟨![-z 1, 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [DihedralLatticeForm.secondReflectionMatrix,
      DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
      dihedralReflectionMatrix6, rotationMatrix6, rotationMatrix,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] <;> omega

lemma not_matrixReflectionIsCentered_orderTwoPrimitive_first :
    ¬ MatrixReflectionIsCentered
      DihedralLatticeForm.orderTwoPrimitive.reflectionMatrix := by
  intro h
  have hz : DihedralLatticeForm.orderTwoPrimitive.reflectionMatrix *ᵥ ![1, 0] =
      ![1, 0] := by decide
  obtain ⟨w, hw⟩ := h ![1, 0] hz
  have h0 := congrFun hw 0
  simp [DihedralLatticeForm.reflectionMatrix,
    IntegralReflection.reflectionLatticeMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at h0
  omega

lemma not_matrixReflectionIsCentered_orderTwoPrimitive_second :
    ¬ MatrixReflectionIsCentered
      DihedralLatticeForm.orderTwoPrimitive.secondReflectionMatrix := by
  intro h
  have hz : DihedralLatticeForm.orderTwoPrimitive.secondReflectionMatrix *ᵥ ![0, 1] =
      ![0, 1] := by decide
  obtain ⟨w, hw⟩ := h ![0, 1] hz
  have h1 := congrFun hw 1
  simp [DihedralLatticeForm.secondReflectionMatrix,
    DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
    IntegralReflection.reflectionLatticeMatrix, dihedralRotationMatrix2,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] at h1
  omega

lemma not_matrixReflectionIsCentered_orderFour_first :
    ¬ MatrixReflectionIsCentered DihedralLatticeForm.orderFour.reflectionMatrix := by
  simpa [DihedralLatticeForm.reflectionMatrix, dihedralReflectionMatrix4,
    IntegralReflection.reflectionLatticeMatrix] using
    not_matrixReflectionIsCentered_orderTwoPrimitive_first

namespace PlaneGroup

/-- The lattice generated by the axes of a selected adjacent pair of reflections. -/
def adjacentReflectionAxisSpan (G : PlaneGroup)
    (s t : pointGroup G.carrier) : Submodule ℤ G.translationLattice.carrier :=
  G.reflectionFixedSubmodule s ⊔ G.reflectionFixedSubmodule t

/-- The intrinsic span of the fixed lattices of all orientation-reversing point elements. -/
def reflectionAxisSpan (G : PlaneGroup) : Submodule ℤ G.translationLattice.carrier :=
  ⨆ (s : pointGroup G.carrier) (_ : s ∉ orientationPreservingPointGroup G),
    G.reflectionFixedSubmodule s

/-- Coordinate-sum character modulo three.  For the `p31m` normal form its kernel is exactly
the global reflection-axis span. -/
def coordinateSumModThree (G : PlaneGroup)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier) :
    G.translationLattice.carrier →ₗ[ℤ] ZMod 3 where
  toFun t := (b.repr t 0 : ZMod 3) + (b.repr t 1 : ZMod 3)
  map_add' x y := by simp; ring
  map_smul' a x := by simp [smul_add, mul_add, add_mul, mul_comm]

lemma reflectionFixedSubmodule_le_reflectionAxisSpan
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G) :
    G.reflectionFixedSubmodule s ≤ G.reflectionAxisSpan :=
  le_iSup_of_le s (le_iSup_of_le hs le_rfl)

/-- A translation-preserving isomorphism carries each fixed-axis lattice onto the corresponding
fixed-axis lattice. -/
theorem reflectionFixedSubmodule_map
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (s : pointGroup G.carrier) :
    Submodule.map e.translationLatticeEquiv.toLinearMap
        (G.reflectionFixedSubmodule s) =
      H.reflectionFixedSubmodule (e.pointGroupEquiv s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ G.reflectionFixedSubmodule s at hx
    change e.translationLatticeEquiv x ∈
      H.reflectionFixedSubmodule (e.pointGroupEquiv s)
    rw [G.mem_reflectionFixedSubmodule_iff] at hx
    rw [H.mem_reflectionFixedSubmodule_iff]
    rw [← e.translationLattice_pointAction, hx]
  · intro hy
    change y ∈ H.reflectionFixedSubmodule (e.pointGroupEquiv s) at hy
    rw [H.mem_reflectionFixedSubmodule_iff] at hy
    refine ⟨e.translationLatticeEquiv.symm y, ?_, by simp⟩
    change e.translationLatticeEquiv.symm y ∈ G.reflectionFixedSubmodule s
    rw [G.mem_reflectionFixedSubmodule_iff]
    apply e.translationLatticeEquiv.injective
    rw [e.translationLattice_pointAction]
    simpa using hy

/-- The selected adjacent-axis span is functorial under translation-preserving isomorphism. -/
theorem adjacentReflectionAxisSpan_map
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (s t : pointGroup G.carrier) :
    Submodule.map e.translationLatticeEquiv.toLinearMap
        (G.adjacentReflectionAxisSpan s t) =
      H.adjacentReflectionAxisSpan (e.pointGroupEquiv s) (e.pointGroupEquiv t) := by
  rw [adjacentReflectionAxisSpan, Submodule.map_sup,
    reflectionFixedSubmodule_map e s, reflectionFixedSubmodule_map e t,
    adjacentReflectionAxisSpan]

/-- The global reflection-axis span is intrinsic under translation-preserving equivalence. -/
theorem reflectionAxisSpan_map
    {G H : PlaneGroup} (e : TranslationPreservingIso G H) :
    Submodule.map e.translationLatticeEquiv.toLinearMap G.reflectionAxisSpan =
      H.reflectionAxisSpan := by
  apply le_antisymm
  · rw [reflectionAxisSpan, Submodule.map_iSup]
    refine iSup_le fun s => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hs => ?_
    rw [reflectionFixedSubmodule_map e s]
    have hs' : e.pointGroupEquiv s ∉ orientationPreservingPointGroup H := by
      intro hm
      exact hs ((e.pointGroupEquiv_mem_orientationPreserving_iff s).1 hm)
    exact le_iSup_of_le (e.pointGroupEquiv s) (le_iSup_of_le hs' le_rfl)
  · rw [reflectionAxisSpan]
    refine iSup_le fun t => ?_
    refine iSup_le fun ht => ?_
    let s : pointGroup G.carrier := e.pointGroupEquiv.symm t
    have hs : s ∉ orientationPreservingPointGroup G := by
      intro hm
      apply ht
      have := (e.pointGroupEquiv_mem_orientationPreserving_iff s).2 hm
      simpa [s] using this
    calc
      H.reflectionFixedSubmodule t =
          Submodule.map e.translationLatticeEquiv.toLinearMap
            (G.reflectionFixedSubmodule s) := by
        rw [reflectionFixedSubmodule_map e s]
        simp [s]
      _ ≤ Submodule.map e.translationLatticeEquiv.toLinearMap G.reflectionAxisSpan :=
        Submodule.map_mono (G.reflectionFixedSubmodule_le_reflectionAxisSpan s hs)

/-- Every lattice vector fixed by `s` is in the image of its reflection norm. -/
def ReflectionActionIsCentered (G : PlaneGroup)
    (s : pointGroup G.carrier) : Prop :=
  ∀ t : G.translationLattice.carrier, G.latticeAction s t = t →
    ∃ u : G.translationLattice.carrier, u + G.latticeAction s u = t

/-- Intrinsic centeredness is preserved by a translation-preserving isomorphism. -/
theorem reflectionActionIsCentered_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (s : pointGroup G.carrier) (hs : G.ReflectionActionIsCentered s) :
    H.ReflectionActionIsCentered (e.pointGroupEquiv s) := by
  intro t ht
  let tG : G.translationLattice.carrier := e.translationLatticeEquiv.symm t
  have htG : G.latticeAction s tG = tG := by
    apply e.translationLatticeEquiv.injective
    rw [e.translationLattice_pointAction]
    simpa [tG] using ht
  obtain ⟨u, hu⟩ := hs tG htG
  refine ⟨e.translationLatticeEquiv u, ?_⟩
  rw [← e.translationLattice_pointAction,
    ← e.translationLatticeEquiv.map_add, hu]
  exact e.translationLatticeEquiv.apply_symm_apply t

/-- Intrinsic centeredness is invariant under translation-preserving isomorphism. -/
theorem reflectionActionIsCentered_iff_of_iso
    {G H : PlaneGroup} (e : TranslationPreservingIso G H)
    (s : pointGroup G.carrier) :
    G.ReflectionActionIsCentered s ↔
      H.ReflectionActionIsCentered (e.pointGroupEquiv s) := by
  constructor
  · exact reflectionActionIsCentered_of_iso e s
  · intro hs
    have hback := reflectionActionIsCentered_of_iso e.symm
      (e.pointGroupEquiv s) hs
    simpa using hback

/-- Matrix centeredness in any integral basis is the intrinsic centeredness of the lattice
action. -/
lemma reflectionActionIsCentered_of_toMatrix
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hmat : LinearMap.toMatrix b b (G.latticeAction s).toLinearMap = M)
    (hM : MatrixReflectionIsCentered M) :
    G.ReflectionActionIsCentered s := by
  intro t ht
  have hfixed : M *ᵥ ⇑(b.repr t) = ⇑(b.repr t) := by
    have h := LinearMap.toMatrix_mulVec_repr b b
      (G.latticeAction s).toLinearMap t
    rw [hmat] at h
    exact h.trans (congrArg (fun x => ⇑(b.repr x)) ht)
  obtain ⟨w, hw⟩ := hM (b.repr t) hfixed
  let u : G.translationLattice.carrier := b.equivFun.symm w
  refine ⟨u, ?_⟩
  apply b.repr.injective
  ext i
  have hu : ⇑(b.repr u) = w := b.equivFun.apply_symm_apply w
  have haction := LinearMap.toMatrix_mulVec_repr b b
    (G.latticeAction s).toLinearMap u
  rw [hmat, hu] at haction
  have haction_i := congrFun haction i
  simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  calc
    (b.repr u) i + (b.repr (G.latticeAction s u)) i =
        w i + (M *ᵥ w) i := by
      rw [congrFun hu i]
      congr 1
      simpa using haction_i.symm
    _ = (b.repr t) i := congrFun hw i

/-- Conversely, intrinsic centeredness can be read in the coordinates of any integral basis. -/
lemma matrixReflectionIsCentered_of_reflectionAction
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hmat : LinearMap.toMatrix b b (G.latticeAction s).toLinearMap = M)
    (hs : G.ReflectionActionIsCentered s) :
    MatrixReflectionIsCentered M := by
  intro z hz
  let t : G.translationLattice.carrier := b.equivFun.symm z
  have htcoords : ⇑(b.repr t) = z := b.equivFun.apply_symm_apply z
  have haction_t := LinearMap.toMatrix_mulVec_repr b b
    (G.latticeAction s).toLinearMap t
  rw [hmat] at haction_t
  have ht : G.latticeAction s t = t := by
    apply b.equivFun.injective
    exact haction_t.symm.trans ((congrArg (fun w => M *ᵥ w) htcoords).trans
      (hz.trans htcoords.symm))
  obtain ⟨u, hu⟩ := hs t ht
  refine ⟨b.repr u, ?_⟩
  have haction_u := LinearMap.toMatrix_mulVec_repr b b
    (G.latticeAction s).toLinearMap u
  rw [hmat] at haction_u
  calc
    ⇑(b.repr u) + M *ᵥ ⇑(b.repr u) =
        ⇑(b.repr u) + ⇑(b.repr (G.latticeAction s u)) :=
      congrArg (fun w => ⇑(b.repr u) + w) haction_u
    _ = ⇑(b.repr (u + G.latticeAction s u)) := by simp
    _ = ⇑(b.repr t) := congrArg (fun x => ⇑(b.repr x)) hu
    _ = z := htcoords

/-- Centeredness is independent of the chosen integral coordinates. -/
theorem matrixReflectionIsCentered_iff_reflectionAction
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hmat : LinearMap.toMatrix b b (G.latticeAction s).toLinearMap = M) :
    MatrixReflectionIsCentered M ↔ G.ReflectionActionIsCentered s :=
  ⟨G.reflectionActionIsCentered_of_toMatrix s b M hmat,
    G.matrixReflectionIsCentered_of_reflectionAction s b M hmat⟩

/-- An arbitrary one-reflection normal form is centered exactly when the intrinsic norm map
surjects onto the fixed lattice. -/
theorem reflectionActionIsCentered_iff_normalForm_kind_centered
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (N : G.ReflectionLatticeNormalForm s) :
    G.ReflectionActionIsCentered s ↔ N.kind = .centered := by
  constructor
  · intro hc
    cases hkind : N.kind with
    | centered => rfl
    | primitive =>
        exfalso
        have hfixed := N.primitive_basis_zero_mem_fixed hkind
        obtain ⟨u, hu⟩ := hc (N.basis 0)
          ((G.mem_reflectionFixedSubmodule_iff s (N.basis 0)).mp hfixed)
        apply N.primitive_basis_zero_not_mem_reflectionNormRange hkind
        exact (G.mem_reflectionNormRange_iff s (N.basis 0)).2 ⟨u, hu⟩
  · intro hkind t ht
    exact N.centered_fixed_is_reflectionNorm hkind
      ((G.mem_reflectionFixedSubmodule_iff s t).2 ht)

/-- Obtain a centered one-reflection normal form from the intrinsic centeredness criterion. -/
theorem exists_centered_reflectionLatticeNormalForm
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G)
    (hc : G.ReflectionActionIsCentered s) :
    ∃ N : G.ReflectionLatticeNormalForm s, N.kind = .centered := by
  obtain ⟨N⟩ := G.exists_reflectionLatticeNormalForm s hs
  exact ⟨N, (G.reflectionActionIsCentered_iff_normalForm_kind_centered s N).mp hc⟩

/-- Obtain a primitive one-reflection normal form when centeredness fails. -/
theorem exists_primitive_reflectionLatticeNormalForm
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G)
    (hc : ¬ G.ReflectionActionIsCentered s) :
    ∃ N : G.ReflectionLatticeNormalForm s, N.kind = .primitive := by
  obtain ⟨N⟩ := G.exists_reflectionLatticeNormalForm s hs
  refine ⟨N, ?_⟩
  cases hkind : N.kind with
  | primitive => rfl
  | centered =>
      exact (hc ((G.reflectionActionIsCentered_iff_normalForm_kind_centered s N).2
        hkind)).elim

lemma latticeAction_toMatrix_mul (G : PlaneGroup)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (h k : pointGroup G.carrier) :
    LinearMap.toMatrix b b (G.latticeAction (h * k)).toLinearMap =
      LinearMap.toMatrix b b (G.latticeAction h).toLinearMap *
        LinearMap.toMatrix b b (G.latticeAction k).toLinearMap := by
  rw [G.latticeAction_mul]
  change LinearMap.toMatrix b b
    ((G.latticeAction h).toLinearMap * (G.latticeAction k).toLinearMap) = _
  exact LinearMap.toMatrix_mul b _ _

lemma latticeAction_toMatrix_one (G : PlaneGroup)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier) :
    LinearMap.toMatrix b b (G.latticeAction 1).toLinearMap = 1 := by
  rw [G.latticeAction_one]
  exact LinearMap.toMatrix_one b

lemma latticeAction_toMatrix_pow (G : PlaneGroup)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (h : pointGroup G.carrier) (n : ℕ) :
    LinearMap.toMatrix b b (G.latticeAction (h ^ n)).toLinearMap =
      (LinearMap.toMatrix b b (G.latticeAction h).toLinearMap) ^ n := by
  induction n with
  | zero => simp [G.latticeAction_toMatrix_one]
  | succ n ih =>
      rw [pow_succ, G.latticeAction_toMatrix_mul, ih, pow_succ]

lemma latticeAction_inverse_toMatrix
    (G : PlaneGroup) (r : pointGroup G.carrier)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier) (c : ℤ)
    (hrot : LinearMap.toMatrix b b (G.latticeAction r).toLinearMap =
      rotationMatrix c) :
    LinearMap.toMatrix b b (G.latticeAction r⁻¹).toLinearMap =
      dihedralRotationInverseMatrix c := by
  let Rinv := LinearMap.toMatrix b b (G.latticeAction r⁻¹).toLinearMap
  have hprod : Rinv * rotationMatrix c = 1 := by
    calc
      Rinv * rotationMatrix c =
          LinearMap.toMatrix b b (G.latticeAction r⁻¹).toLinearMap *
            LinearMap.toMatrix b b (G.latticeAction r).toLinearMap := by rw [hrot]
      _ = LinearMap.toMatrix b b (G.latticeAction (r⁻¹ * r)).toLinearMap :=
        (G.latticeAction_toMatrix_mul b r⁻¹ r).symm
      _ = 1 := by simpa using G.latticeAction_toMatrix_one b
  calc
    Rinv = Rinv * 1 := (mul_one Rinv).symm
    _ = Rinv * (rotationMatrix c * dihedralRotationInverseMatrix c) := by rw [rotationMatrix_mul_dihedralRotationInverseMatrix]
    _ = (Rinv * rotationMatrix c) * dihedralRotationInverseMatrix c := by rw [mul_assoc]
    _ = dihedralRotationInverseMatrix c := by rw [hprod, one_mul]

/-- In a rotation normal-form basis, a reversing generator satisfies `B A = A⁻¹ B`. -/
lemma reversing_matrix_relation
    (G : PlaneGroup) (d : DihedralGenerators G)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier) (c : ℤ)
    (hrot : LinearMap.toMatrix b b (G.latticeAction d.rotation.1).toLinearMap =
      rotationMatrix c) :
    LinearMap.toMatrix b b (G.latticeAction d.reflection).toLinearMap *
        rotationMatrix c =
      dihedralRotationInverseMatrix c *
        LinearMap.toMatrix b b (G.latticeAction d.reflection).toLinearMap := by
  let B := LinearMap.toMatrix b b (G.latticeAction d.reflection).toLinearMap
  have hinv := G.latticeAction_inverse_toMatrix d.rotation.1 b c hrot
  calc
    B * rotationMatrix c =
        LinearMap.toMatrix b b
          (G.latticeAction (d.reflection * d.rotation.1)).toLinearMap := by
      rw [G.latticeAction_toMatrix_mul, hrot]
    _ = LinearMap.toMatrix b b
          (G.latticeAction ((d.rotation.1)⁻¹ * d.reflection)).toLinearMap := by
      rw [d.reflection_mul_rotation]
    _ = dihedralRotationInverseMatrix c * B := by
      rw [G.latticeAction_toMatrix_mul, hinv]

/-- The determinant of a reversing action is `-1` in every integer basis. -/
lemma reversing_toMatrix_det
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier) :
    (LinearMap.toMatrix b b (G.latticeAction s).toLinearMap).det = -1 := by
  calc
    _ = LinearMap.det (G.latticeAction s).toLinearMap :=
      LinearMap.det_toMatrix b (G.latticeAction s).toLinearMap
    _ = (G.latticeActionMatrix s).det := by
      simp [latticeActionMatrix, RankTwoLattice.equivMatrix]
    _ = -1 := G.reversing_integral_det_eq_neg_one s hs

/-- A lattice basis simultaneously normalizing a positive generator and an adjacent reflection. -/
structure DihedralLatticeNormalForm (G : PlaneGroup) (d : DihedralGenerators G) where
  form : DihedralLatticeForm
  order_eq : form.order = d.order
  basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier
  rotation_matrix_eq :
    LinearMap.toMatrix basis basis (G.latticeAction d.rotation.1).toLinearMap =
      form.rotationMatrix
  reflection_matrix_eq :
    LinearMap.toMatrix basis basis (G.latticeAction d.reflection).toLinearMap =
      form.reflectionMatrix
  secondReflection_matrix_eq :
    LinearMap.toMatrix basis basis (G.latticeAction d.secondReflection).toLinearMap =
      form.secondReflectionMatrix

namespace DihedralLatticeNormalForm

variable {G : PlaneGroup} {d : DihedralGenerators G}

lemma firstReflection_action_coordinates
    (N : DihedralLatticeNormalForm G d)
    (t : G.translationLattice.carrier) :
    ⇑(N.basis.repr (G.latticeAction d.reflection t)) =
      N.form.reflectionMatrix *ᵥ ⇑(N.basis.repr t) := by
  have h := LinearMap.toMatrix_mulVec_repr N.basis N.basis
    (G.latticeAction d.reflection).toLinearMap t
  rw [N.reflection_matrix_eq] at h
  exact h.symm

lemma secondReflection_action_coordinates
    (N : DihedralLatticeNormalForm G d)
    (t : G.translationLattice.carrier) :
    ⇑(N.basis.repr (G.latticeAction d.secondReflection t)) =
      N.form.secondReflectionMatrix *ᵥ ⇑(N.basis.repr t) := by
  have h := LinearMap.toMatrix_mulVec_repr N.basis N.basis
    (G.latticeAction d.secondReflection).toLinearMap t
  rw [N.secondReflection_matrix_eq] at h
  exact h.symm

lemma firstReflection_centered_of_matrix
    (N : DihedralLatticeNormalForm G d)
    (h : MatrixReflectionIsCentered N.form.reflectionMatrix) :
    G.ReflectionActionIsCentered d.reflection :=
  G.reflectionActionIsCentered_of_toMatrix d.reflection N.basis
    N.form.reflectionMatrix N.reflection_matrix_eq h

lemma secondReflection_centered_of_matrix
    (N : DihedralLatticeNormalForm G d)
    (h : MatrixReflectionIsCentered N.form.secondReflectionMatrix) :
    G.ReflectionActionIsCentered d.secondReflection :=
  G.reflectionActionIsCentered_of_toMatrix d.secondReflection N.basis
    N.form.secondReflectionMatrix N.secondReflection_matrix_eq h

lemma firstReflection_not_centered_of_matrix
    (N : DihedralLatticeNormalForm G d)
    (h : ¬ MatrixReflectionIsCentered N.form.reflectionMatrix) :
    ¬ G.ReflectionActionIsCentered d.reflection := by
  intro hc
  apply h
  exact G.matrixReflectionIsCentered_of_reflectionAction d.reflection N.basis
    N.form.reflectionMatrix N.reflection_matrix_eq hc

lemma secondReflection_not_centered_of_matrix
    (N : DihedralLatticeNormalForm G d)
    (h : ¬ MatrixReflectionIsCentered N.form.secondReflectionMatrix) :
    ¬ G.ReflectionActionIsCentered d.secondReflection := by
  intro hc
  apply h
  exact G.matrixReflectionIsCentered_of_reflectionAction d.secondReflection N.basis
    N.form.secondReflectionMatrix N.secondReflection_matrix_eq hc

/-- In the `p3m1` form the two adjacent primitive reflection axes already generate the entire
translation lattice. -/
theorem p3m1_adjacentReflectionAxisSpan_eq_top
    (N : DihedralLatticeNormalForm G d) (hform : N.form = .p3m1) :
    G.adjacentReflectionAxisSpan d.reflection d.secondReflection = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem N.basis).2
  intro i
  fin_cases i
  · have hfix : N.basis 0 ∈ G.reflectionFixedSubmodule d.reflection := by
      rw [G.mem_reflectionFixedSubmodule_iff]
      apply N.basis.equivFun.injective
      change ⇑(N.basis.repr (G.latticeAction d.reflection (N.basis 0))) =
        ⇑(N.basis.repr (N.basis 0))
      rw [N.firstReflection_action_coordinates]
      funext j
      fin_cases j <;>
        simp [hform, DihedralLatticeForm.reflectionMatrix,
          dihedralReflectionMatrix3Full, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
    exact (le_sup_left : G.reflectionFixedSubmodule d.reflection ≤
      G.adjacentReflectionAxisSpan d.reflection d.secondReflection) hfix
  · have hfix : N.basis 1 ∈ G.reflectionFixedSubmodule d.secondReflection := by
      rw [G.mem_reflectionFixedSubmodule_iff]
      apply N.basis.equivFun.injective
      change ⇑(N.basis.repr (G.latticeAction d.secondReflection (N.basis 1))) =
        ⇑(N.basis.repr (N.basis 1))
      rw [N.secondReflection_action_coordinates]
      funext j
      fin_cases j <;>
        simp [hform, DihedralLatticeForm.secondReflectionMatrix,
          DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
          dihedralReflectionMatrix3Full, rotationMatrix3, rotationMatrix,
          Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]
    exact (le_sup_right : G.reflectionFixedSubmodule d.secondReflection ≤
      G.adjacentReflectionAxisSpan d.reflection d.secondReflection) hfix

/-- In the `p3m1` form the intrinsic span of all reflection axes is the full translation
lattice. -/
theorem p3m1_reflectionAxisSpan_eq_top
    (N : DihedralLatticeNormalForm G d) (hform : N.form = .p3m1) :
    G.reflectionAxisSpan = ⊤ := by
  apply top_unique
  rw [← N.p3m1_adjacentReflectionAxisSpan_eq_top hform]
  exact sup_le
    (G.reflectionFixedSubmodule_le_reflectionAxisSpan d.reflection
      d.reflection_reversing)
    (G.reflectionFixedSubmodule_le_reflectionAxisSpan d.secondReflection
      d.secondReflection_reversing)

/-- For `p31m`, the two adjacent reflection axes generate the kernel of coordinate sum modulo
three.  This gives a basis-independent description after transport. -/
theorem p31m_adjacentReflectionAxisSpan_eq_ker
    (N : DihedralLatticeNormalForm G d) (hform : N.form = .p31m) :
    G.adjacentReflectionAxisSpan d.reflection d.secondReflection =
      LinearMap.ker (G.coordinateSumModThree N.basis) := by
  apply le_antisymm
  · apply sup_le
    · intro t ht
      rw [LinearMap.mem_ker]
      rw [G.mem_reflectionFixedSubmodule_iff] at ht
      have hcoord := N.firstReflection_action_coordinates t
      rw [ht] at hcoord
      have h0 := congrFun hcoord 0
      have h1 := congrFun hcoord 1
      simp [hform, DihedralLatticeForm.reflectionMatrix,
        dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
      change (N.basis.repr t 0 : ZMod 3) + (N.basis.repr t 1 : ZMod 3) = 0
      rw [← Int.cast_add]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2
      refine ⟨N.basis.repr t 0, ?_⟩
      omega
    · intro t ht
      rw [LinearMap.mem_ker]
      rw [G.mem_reflectionFixedSubmodule_iff] at ht
      have hcoord := N.secondReflection_action_coordinates t
      rw [ht] at hcoord
      have h0 := congrFun hcoord 0
      have h1 := congrFun hcoord 1
      simp [hform, DihedralLatticeForm.secondReflectionMatrix,
        DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
        dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
        rotationMatrix3, rotationMatrix, Matrix.mulVec, Matrix.mul_apply,
        dotProduct, Fin.sum_univ_two] at h0 h1
      change (N.basis.repr t 0 : ZMod 3) + (N.basis.repr t 1 : ZMod 3) = 0
      rw [← Int.cast_add]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2
      refine ⟨N.basis.repr t 1, ?_⟩
      omega
  · intro t ht
    rw [LinearMap.mem_ker] at ht
    have hcast : ((N.basis.repr t 0 + N.basis.repr t 1 : ℤ) : ZMod 3) = 0 := by
      simpa [coordinateSumModThree] using ht
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (N.basis.repr t 0 + N.basis.repr t 1) 3).1 hcast
    let u : G.translationLattice.carrier := N.basis 0 + (2 : ℤ) • N.basis 1
    let v : G.translationLattice.carrier := (2 : ℤ) • N.basis 0 + N.basis 1
    have hu : u ∈ G.reflectionFixedSubmodule d.reflection := by
      rw [G.mem_reflectionFixedSubmodule_iff]
      apply N.basis.equivFun.injective
      change ⇑(N.basis.repr (G.latticeAction d.reflection u)) = ⇑(N.basis.repr u)
      rw [N.firstReflection_action_coordinates]
      funext j
      fin_cases j <;>
        simp [u, hform, DihedralLatticeForm.reflectionMatrix,
          dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hv : v ∈ G.reflectionFixedSubmodule d.secondReflection := by
      rw [G.mem_reflectionFixedSubmodule_iff]
      apply N.basis.equivFun.injective
      change ⇑(N.basis.repr (G.latticeAction d.secondReflection v)) =
        ⇑(N.basis.repr v)
      rw [N.secondReflection_action_coordinates]
      funext j
      fin_cases j <;>
        simp [v, hform, DihedralLatticeForm.secondReflectionMatrix,
          DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
          dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
          rotationMatrix3, rotationMatrix, Matrix.mulVec, Matrix.mul_apply,
          dotProduct, Fin.sum_univ_two]
    have hmem :
        (2 * k - N.basis.repr t 0) • u +
            (N.basis.repr t 0 - k) • v ∈
          G.adjacentReflectionAxisSpan d.reflection d.secondReflection :=
      (G.adjacentReflectionAxisSpan d.reflection d.secondReflection).add_mem
        ((G.adjacentReflectionAxisSpan d.reflection d.secondReflection).smul_mem _
          ((le_sup_left : G.reflectionFixedSubmodule d.reflection ≤
            G.adjacentReflectionAxisSpan d.reflection d.secondReflection) hu))
        ((G.adjacentReflectionAxisSpan d.reflection d.secondReflection).smul_mem _
          ((le_sup_right : G.reflectionFixedSubmodule d.secondReflection ≤
            G.adjacentReflectionAxisSpan d.reflection d.secondReflection) hv))
    have heq :
        (2 * k - N.basis.repr t 0) • u +
            (N.basis.repr t 0 - k) • v = t := by
      apply N.basis.repr.injective
      ext j
      fin_cases j <;> simp [u, v] <;> omega
    rw [← heq]
    exact hmem

/-- In an order-three `p31m` form, every reversing element fixes only vectors in the same
modulo-three kernel. -/
theorem p31m_reflectionFixedSubmodule_le_ker
    (N : DihedralLatticeNormalForm G d) (hform : N.form = .p31m)
    (s : pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G) :
    G.reflectionFixedSubmodule s ≤
      LinearMap.ker (G.coordinateSumModThree N.basis) := by
  classical
  intro t ht
  rcases d.point_two_coset_normal_form s with
    ⟨r, -, hrs⟩ | ⟨r, hr, hrs⟩
  · exfalso
    apply hs
    rw [hrs]
    exact r.2
  · have hdorder : d.order = .three := by
      rw [← N.order_eq, hform]
      rfl
    have horderPoint : orderOf d.rotation.1 = 3 := by
      simpa [hdorder, DihedralRotationOrder.toNat] using d.rotation_order
    have horder : orderOf d.rotation = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact horderPoint
    have hfin : IsOfFinOrder d.rotation :=
      orderOf_ne_zero_iff.mp (by omega)
    have hrange := (hfin.mem_zpowers_iff_mem_range_orderOf).1 hr
    rw [horder] at hrange
    simp only [Finset.mem_image, Finset.mem_range] at hrange
    obtain ⟨n, hn, hpow⟩ := hrange
    have hpowval : d.rotation.1 ^ n = r.1 := by
      simpa using congrArg Subtype.val hpow
    have hrs' : s = d.reflection * d.rotation.1 ^ n := by
      rw [hrs, hpowval]
    have hmat : LinearMap.toMatrix N.basis N.basis
          (G.latticeAction s).toLinearMap =
        N.form.reflectionMatrix * N.form.rotationMatrix ^ n := by
      rw [hrs', G.latticeAction_toMatrix_mul, G.latticeAction_toMatrix_pow,
        N.reflection_matrix_eq, N.rotation_matrix_eq]
    rw [G.mem_reflectionFixedSubmodule_iff] at ht
    have hcoord := LinearMap.toMatrix_mulVec_repr N.basis N.basis
      (G.latticeAction s).toLinearMap t
    rw [hmat] at hcoord
    have hcoord := hcoord.trans (congrArg (fun x => ⇑(N.basis.repr x)) ht)
    have h0 := congrFun hcoord 0
    have h1 := congrFun hcoord 1
    have hdiv : (3 : ℤ) ∣ N.basis.repr t 0 + N.basis.repr t 1 := by
      interval_cases n
      · simp [hform, DihedralLatticeForm.reflectionMatrix,
          DihedralLatticeForm.rotationMatrix,
          dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
          rotationMatrix3, rotationMatrix, Matrix.mulVec, Matrix.mul_apply,
          dotProduct, Fin.sum_univ_two] at h0 h1
        refine ⟨N.basis.repr t 0, ?_⟩
        omega
      · simp [hform, DihedralLatticeForm.reflectionMatrix,
          DihedralLatticeForm.rotationMatrix,
          dihedralReflectionMatrix3IndexThree, dihedralReflectionMatrix3Full,
          rotationMatrix3, rotationMatrix, Matrix.mulVec, Matrix.mul_apply,
          dotProduct, Fin.sum_univ_two] at h0 h1
        refine ⟨N.basis.repr t 1, ?_⟩
        omega
      · have hm2 :
            DihedralLatticeForm.p31m.reflectionMatrix *
                DihedralLatticeForm.p31m.rotationMatrix ^ 2 =
              !![0, -1; -1, 0] := by decide
        rw [hform, hm2] at h0 h1
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
        refine ⟨0, ?_⟩
        omega
    rw [LinearMap.mem_ker]
    change (N.basis.repr t 0 : ZMod 3) + (N.basis.repr t 1 : ZMod 3) = 0
    rw [← Int.cast_add]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hdiv

/-- The global axis span of `p31m` is exactly the index-three coordinate kernel. -/
theorem p31m_reflectionAxisSpan_eq_ker
    (N : DihedralLatticeNormalForm G d) (hform : N.form = .p31m) :
    G.reflectionAxisSpan = LinearMap.ker (G.coordinateSumModThree N.basis) := by
  apply le_antisymm
  · rw [PlaneGroup.reflectionAxisSpan]
    exact iSup_le fun s => iSup_le fun hs =>
      N.p31m_reflectionFixedSubmodule_le_ker hform s hs
  · rw [← N.p31m_adjacentReflectionAxisSpan_eq_ker hform]
    exact sup_le
      (G.reflectionFixedSubmodule_le_reflectionAxisSpan d.reflection
        d.reflection_reversing)
      (G.reflectionFixedSubmodule_le_reflectionAxisSpan d.secondReflection
        d.secondReflection_reversing)

lemma coordinateSumModThree_surjective
    (G : PlaneGroup)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier) :
    Function.Surjective (G.coordinateSumModThree b) := by
  intro z
  let t : G.translationLattice.carrier :=
    b.equivFun.symm ![ZMod.cast z, 0]
  refine ⟨t, ?_⟩
  have ht : ⇑(b.repr t) = ![ZMod.cast z, 0] :=
    b.equivFun.apply_symm_apply _
  change (b.repr t 0 : ZMod 3) + (b.repr t 1 : ZMod 3) = z
  rw [congrFun ht 0, congrFun ht 1]
  simp [ZMod.intCast_zmod_cast]

/-- The quotient by the `p31m` reflection-axis span is canonically a three-element module. -/
noncomputable def p31m_reflectionAxisQuotientEquivZMod
    (N : DihedralLatticeNormalForm G d) (hform : N.form = .p31m) :
    (G.translationLattice.carrier ⧸ G.reflectionAxisSpan) ≃ₗ[ℤ] ZMod 3 :=
  (Submodule.quotEquivOfEq G.reflectionAxisSpan
      (LinearMap.ker (G.coordinateSumModThree N.basis))
      (N.p31m_reflectionAxisSpan_eq_ker hform)).trans
    ((G.coordinateSumModThree N.basis).quotKerEquivOfSurjective
      (coordinateSumModThree_surjective G N.basis))

/-- The `p31m` global axis span is proper. -/
theorem p31m_reflectionAxisSpan_ne_top
    (N : DihedralLatticeNormalForm G d) (hform : N.form = .p31m) :
    G.reflectionAxisSpan ≠ ⊤ := by
  intro htop
  have hker : LinearMap.ker (G.coordinateSumModThree N.basis) = ⊤ :=
    (N.p31m_reflectionAxisSpan_eq_ker hform).symm.trans htop
  have hb : N.basis 0 ∈ LinearMap.ker (G.coordinateSumModThree N.basis) := by
    rw [hker]
    trivial
  rw [LinearMap.mem_ker] at hb
  norm_num [coordinateSumModThree] at hb

/-- The intrinsic `p31m` axis quotient has cardinality three. -/
theorem p31m_reflectionAxisQuotient_natCard
    (N : DihedralLatticeNormalForm G d) (hform : N.form = .p31m) :
    Nat.card (G.translationLattice.carrier ⧸ G.reflectionAxisSpan) = 3 := by
  calc
    Nat.card (G.translationLattice.carrier ⧸ G.reflectionAxisSpan) =
        Nat.card (ZMod 3) :=
      Nat.card_congr (N.p31m_reflectionAxisQuotientEquivZMod hform).toEquiv
    _ = 3 := Nat.card_zmod 3

/-- The two order-three reflection-axis embeddings cannot be translation-preservingly
equivalent. -/
theorem p3m1_not_equivalent_p31m
    {G H : PlaneGroup} {dG : DihedralGenerators G} {dH : DihedralGenerators H}
    (NG : DihedralLatticeNormalForm G dG) (hG : NG.form = .p3m1)
    (NH : DihedralLatticeNormalForm H dH) (hH : NH.form = .p31m) :
    ¬ PlaneGroup.Equivalent G H := by
  rintro ⟨e⟩
  apply NH.p31m_reflectionAxisSpan_ne_top hH
  calc
    H.reflectionAxisSpan =
        Submodule.map e.translationLatticeEquiv.toLinearMap G.reflectionAxisSpan :=
      (reflectionAxisSpan_map e).symm
    _ = Submodule.map e.translationLatticeEquiv.toLinearMap ⊤ := by
      rw [NG.p3m1_reflectionAxisSpan_eq_top hG]
    _ = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.translationLatticeEquiv.surjective

/-- A one-reflection normal form for the first generator, with its kind determined by the joint
dihedral form. -/
theorem exists_firstReflectionNormalForm
    (N : DihedralLatticeNormalForm G d) :
    ∃ R : G.ReflectionLatticeNormalForm d.reflection,
      R.kind = N.form.firstReflectionKind := by
  cases hform : N.form with
  | orderTwoPrimitive =>
      obtain ⟨R, hR⟩ := G.exists_primitive_reflectionLatticeNormalForm d.reflection
        d.reflection_reversing (N.firstReflection_not_centered_of_matrix (by
          simpa [hform] using not_matrixReflectionIsCentered_orderTwoPrimitive_first))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.firstReflectionKind] using hR⟩
  | orderTwoCentered =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.reflection
        d.reflection_reversing (N.firstReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_orderTwoCentered_first))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.firstReflectionKind] using hR⟩
  | p3m1 =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.reflection
        d.reflection_reversing (N.firstReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_p3m1_first))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.firstReflectionKind] using hR⟩
  | p31m =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.reflection
        d.reflection_reversing (N.firstReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_p31m_first))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.firstReflectionKind] using hR⟩
  | orderFour =>
      obtain ⟨R, hR⟩ := G.exists_primitive_reflectionLatticeNormalForm d.reflection
        d.reflection_reversing (N.firstReflection_not_centered_of_matrix (by
          simpa [hform] using not_matrixReflectionIsCentered_orderFour_first))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.firstReflectionKind] using hR⟩
  | orderSix =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.reflection
        d.reflection_reversing (N.firstReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_orderSix_first))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.firstReflectionKind] using hR⟩

/-- A one-reflection normal form for the adjacent second generator, with its kind determined by
the joint dihedral form. -/
theorem exists_secondReflectionNormalForm
    (N : DihedralLatticeNormalForm G d) :
    ∃ R : G.ReflectionLatticeNormalForm d.secondReflection,
      R.kind = N.form.secondReflectionKind := by
  cases hform : N.form with
  | orderTwoPrimitive =>
      obtain ⟨R, hR⟩ := G.exists_primitive_reflectionLatticeNormalForm d.secondReflection
        d.secondReflection_reversing (N.secondReflection_not_centered_of_matrix (by
          simpa [hform] using not_matrixReflectionIsCentered_orderTwoPrimitive_second))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.secondReflectionKind] using hR⟩
  | orderTwoCentered =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.secondReflection
        d.secondReflection_reversing (N.secondReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_orderTwoCentered_second))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.secondReflectionKind] using hR⟩
  | p3m1 =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.secondReflection
        d.secondReflection_reversing (N.secondReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_p3m1_second))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.secondReflectionKind] using hR⟩
  | p31m =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.secondReflection
        d.secondReflection_reversing (N.secondReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_p31m_second))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.secondReflectionKind] using hR⟩
  | orderFour =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.secondReflection
        d.secondReflection_reversing (N.secondReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_orderFour_second))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.secondReflectionKind] using hR⟩
  | orderSix =>
      obtain ⟨R, hR⟩ := G.exists_centered_reflectionLatticeNormalForm d.secondReflection
        d.secondReflection_reversing (N.secondReflection_centered_of_matrix (by
          simpa [hform] using matrixReflectionIsCentered_orderSix_second))
      exact ⟨R, by simpa [hform, DihedralLatticeForm.secondReflectionKind] using hR⟩

end DihedralLatticeNormalForm

/-- Assemble the simultaneous normal form once the two generator matrices are known. -/
def DihedralLatticeNormalForm.ofMatrices
    (G : PlaneGroup) (d : DihedralGenerators G) (form : DihedralLatticeForm)
    (horder : form.order = d.order)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier)
    (hrot : LinearMap.toMatrix b b (G.latticeAction d.rotation.1).toLinearMap =
      form.rotationMatrix)
    (href : LinearMap.toMatrix b b (G.latticeAction d.reflection).toLinearMap =
      form.reflectionMatrix) :
    DihedralLatticeNormalForm G d where
  form := form
  order_eq := horder
  basis := b
  rotation_matrix_eq := hrot
  reflection_matrix_eq := href
  secondReflection_matrix_eq := by
    rw [DihedralGenerators.secondReflection, G.latticeAction_toMatrix_mul]
    rw [href, hrot]
    rfl

/-- Matrix of a reflection generator after moving it through its reversing coset by a rotation
power. -/
lemma rotateReflection_toMatrix
    (G : PlaneGroup) (d : DihedralGenerators G)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier) (n : ℕ) :
    LinearMap.toMatrix b b
        (G.latticeAction (d.rotateReflection n).reflection).toLinearMap =
      LinearMap.toMatrix b b (G.latticeAction d.reflection).toLinearMap *
        (LinearMap.toMatrix b b (G.latticeAction d.rotation.1).toLinearMap) ^ n := by
  rw [DihedralGenerators.rotateReflection_reflection,
    G.latticeAction_toMatrix_mul, G.latticeAction_toMatrix_pow]

/-- A positive point element of order two is central inversion on the plane. -/
lemma orientationPreserving_eq_neg_of_order_two (G : PlaneGroup)
    (r : orientationPreservingPointGroup G) (hr : orderOf r.1 = 2) :
    (r.1 : Plane ≃ₗᵢ[ℝ] Plane) = LinearIsometryEquiv.neg ℝ := by
  have htrace : (G.latticeActionMatrix r.1).trace = -2 := by
    rcases G.orientationPreserving_trace_order_cases r with
      h | h | h | h | h
    · exact h.1
    · omega
    · omega
    · omega
    · omega
  apply eq_neg_of_trace_eq_neg_two
  rw [← G.trace_cast r.1]
  exact_mod_cast htrace

/-- In any integer basis, a positive order-two lattice action is `-I`. -/
lemma orderTwo_rotation_toMatrix
    (G : PlaneGroup) (r : orientationPreservingPointGroup G)
    (hr : orderOf r.1 = 2)
    (b : Module.Basis (Fin 2) ℤ G.translationLattice.carrier) :
    LinearMap.toMatrix b b (G.latticeAction r.1).toLinearMap =
      dihedralRotationMatrix2 := by
  have hneg := orientationPreserving_eq_neg_of_order_two G r hr
  ext i j
  rw [LinearMap.toMatrix_apply]
  change b.repr (G.latticeAction r.1 (b j)) i = _
  have hb : G.latticeAction r.1 (b j) = -(b j) := by
    apply Subtype.ext
    rw [G.latticeAction_coe]
    change (r.1 : Plane ≃ₗᵢ[ℝ] Plane) (b j : Plane) = -(b j : Plane)
    rw [hneg]
    rfl
  rw [hb]
  fin_cases i <;> fin_cases j <;>
    simp [dihedralRotationMatrix2]

namespace DihedralLatticeNormalForm

variable {G : PlaneGroup} {d : DihedralGenerators G}

/-- Reindex a rank-two lattice basis by exchanging its two vectors. -/
def swappedBasis (N : DihedralLatticeNormalForm G d) :
    Module.Basis (Fin 2) ℤ G.translationLattice.carrier :=
  N.basis.reindex (Equiv.swap 0 1)

/-- Simultaneously reindexing the source and target basis exchanges the corresponding rows and
columns of a lattice-action matrix. -/
lemma toMatrix_swappedBasis (N : DihedralLatticeNormalForm G d)
    (f : G.translationLattice.carrier →ₗ[ℤ] G.translationLattice.carrier) :
    LinearMap.toMatrix N.swappedBasis N.swappedBasis f =
      (LinearMap.toMatrix N.basis N.basis f).submatrix
        (Equiv.swap 0 1).symm (Equiv.swap 0 1).symm := by
  ext i j
  simp [swappedBasis, LinearMap.toMatrix_apply]

/-- In the primitive order-two form, rotating the reflection generator once exchanges the two
selected reflection points. -/
theorem rotateReflection_one_secondReflection
    (N : DihedralLatticeNormalForm G d)
    (hform : N.form = .orderTwoPrimitive) :
    (d.rotateReflection 1).secondReflection = d.reflection := by
  have horder : d.order = .two := by
    rw [← N.order_eq, hform]
    rfl
  have hrorder : orderOf d.rotation.1 = 2 := by
    simpa [horder, DihedralRotationOrder.toNat] using d.rotation_order
  have hrpow : d.rotation.1 ^ 2 = 1 := by
    simpa [hrorder] using pow_orderOf_eq_one d.rotation.1
  simp only [DihedralGenerators.secondReflection,
    DihedralGenerators.rotateReflection_reflection,
    DihedralGenerators.rotateReflection_rotation, pow_one]
  rw [mul_assoc, show d.rotation.1 * d.rotation.1 = 1 by
    simpa [pow_two] using hrpow]
  simp

/-- Both point-group equalities exhibited by the primitive order-two generator swap. -/
theorem rotateReflection_one_point_equalities
    (N : DihedralLatticeNormalForm G d)
    (hform : N.form = .orderTwoPrimitive) :
    (d.rotateReflection 1).reflection = d.secondReflection ∧
      (d.rotateReflection 1).secondReflection = d.reflection :=
  ⟨d.rotateReflection_one_reflection, N.rotateReflection_one_secondReflection hform⟩

/-- Swap the two primitive reflection generators and the two lattice-basis vectors.  The joint
normal form remains `orderTwoPrimitive`. -/
def swapOrderTwoPrimitive
    (N : DihedralLatticeNormalForm G d)
    (hform : N.form = .orderTwoPrimitive) :
    DihedralLatticeNormalForm G (d.rotateReflection 1) := by
  have horder : d.order = .two := by
    rw [← N.order_eq, hform]
    rfl
  have hrorder : orderOf d.rotation.1 = 2 := by
    simpa [horder, DihedralRotationOrder.toNat] using d.rotation_order
  refine DihedralLatticeNormalForm.ofMatrices G (d.rotateReflection 1)
    .orderTwoPrimitive ?_ N.swappedBasis ?_ ?_
  · change .two = d.order
    exact horder.symm
  · exact orderTwo_rotation_toMatrix G (d.rotateReflection 1).rotation (by
      simpa using hrorder) N.swappedBasis
  · rw [d.rotateReflection_one_reflection, N.toMatrix_swappedBasis,
      N.secondReflection_matrix_eq, hform]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [DihedralLatticeForm.secondReflectionMatrix,
        DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
        IntegralReflection.reflectionLatticeMatrix, dihedralRotationMatrix2,
        Matrix.mul_apply]

@[simp]
theorem swapOrderTwoPrimitive_form
    (N : DihedralLatticeNormalForm G d)
    (hform : N.form = .orderTwoPrimitive) :
    (N.swapOrderTwoPrimitive hform).form = .orderTwoPrimitive :=
  rfl

@[simp]
theorem swapOrderTwoPrimitive_basis
    (N : DihedralLatticeNormalForm G d)
    (hform : N.form = .orderTwoPrimitive) :
    (N.swapOrderTwoPrimitive hform).basis = N.swappedBasis :=
  rfl

end DihedralLatticeNormalForm

/-- The order-two simultaneous form is exactly the primitive/centered form of either selected
reflection. -/
theorem exists_orderTwo_dihedralLatticeNormalForm
    (G : PlaneGroup) (d : DihedralGenerators G) (horder : d.order = .two) :
    Nonempty (DihedralLatticeNormalForm G d) := by
  obtain ⟨N⟩ := G.exists_reflectionLatticeNormalForm d.reflection
    d.reflection_reversing
  have hrorder : orderOf d.rotation.1 = 2 := by
    simpa [horder, DihedralRotationOrder.toNat] using d.rotation_order
  have hrot := orderTwo_rotation_toMatrix G d.rotation hrorder N.basis
  cases hkind : N.kind with
  | primitive =>
      refine ⟨⟨.orderTwoPrimitive, by
        simp [DihedralLatticeForm.order, horder], N.basis, hrot, ?_, ?_⟩⟩
      · simpa [DihedralLatticeForm.reflectionMatrix, hkind] using N.matrix_eq
      · rw [DihedralGenerators.secondReflection, G.latticeAction_mul]
        change LinearMap.toMatrix N.basis N.basis
          ((G.latticeAction d.reflection).toLinearMap *
            (G.latticeAction d.rotation.1).toLinearMap) = _
        rw [LinearMap.toMatrix_mul N.basis]
        rw [N.matrix_eq, hrot]
        simp [DihedralLatticeForm.secondReflectionMatrix,
          DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
          hkind]
  | centered =>
      refine ⟨⟨.orderTwoCentered, by
        simp [DihedralLatticeForm.order, horder], N.basis, hrot, ?_, ?_⟩⟩
      · simpa [DihedralLatticeForm.reflectionMatrix, hkind] using N.matrix_eq
      · rw [DihedralGenerators.secondReflection, G.latticeAction_mul]
        change LinearMap.toMatrix N.basis N.basis
          ((G.latticeAction d.reflection).toLinearMap *
            (G.latticeAction d.rotation.1).toLinearMap) = _
        rw [LinearMap.toMatrix_mul N.basis]
        rw [N.matrix_eq, hrot]
        simp [DihedralLatticeForm.secondReflectionMatrix,
          DihedralLatticeForm.reflectionMatrix, DihedralLatticeForm.rotationMatrix,
          hkind]

/-- After replacing the reversing generator by an adjacent one if necessary, every order-three
dihedral action has exactly one of the `p3m1` and `p31m` joint lattice forms. -/
theorem exists_orderThree_dihedralLatticeNormalForm
    (G : PlaneGroup) (d : DihedralGenerators G) (horder : d.order = .three) :
    ∃ d' : DihedralGenerators G, Nonempty (DihedralLatticeNormalForm G d') := by
  have hrorder : orderOf d.rotation.1 = 3 := by
    simpa [horder, DihedralRotationOrder.toNat] using d.rotation_order
  obtain ⟨R⟩ := G.exists_orderThree_latticeActionNormalForm d.rotation hrorder
  let B := LinearMap.toMatrix R.basis R.basis
    (G.latticeAction d.reflection).toLinearMap
  have hrel : B * rotationMatrix (-1) =
      dihedralRotationInverseMatrix (-1) * B := by
    apply G.reversing_matrix_relation d R.basis (-1)
    simpa [rotationMatrix3] using R.matrix_eq
  have hshape := matrix_eq_of_mul_rotationMatrix_eq_inverse_mul B (-1) hrel
  have hdet : B.det = -1 :=
    G.reversing_toMatrix_det d.reflection d.reflection_reversing R.basis
  have hnorm0 := reflection_norm_equation B (-1) hshape hdet
  have hnorm : B 0 0 ^ 2 + B 0 1 ^ 2 + B 0 0 * B 0 1 = 1 := by
    simpa using hnorm0
  rcases orderThree_shape_normalization (B 0 0) (B 0 1) hnorm with
    ⟨n, hn⟩ | ⟨n, hn⟩
  · let d' := d.rotateReflection n.val
    have href : LinearMap.toMatrix R.basis R.basis
        (G.latticeAction d'.reflection).toLinearMap =
          dihedralReflectionMatrix3Full := by
      rw [G.rotateReflection_toMatrix]
      rw [R.matrix_eq]
      change B * rotationMatrix3 ^ n.val = _
      rw [hshape]
      simpa using hn
    refine ⟨d', ⟨DihedralLatticeNormalForm.ofMatrices G d' .p3m1 ?_
      R.basis ?_ ?_⟩⟩
    · change .three = d.order
      exact horder.symm
    · simpa [d', DihedralLatticeForm.rotationMatrix] using R.matrix_eq
    · simpa [DihedralLatticeForm.reflectionMatrix] using href
  · let d' := d.rotateReflection n.val
    have href : LinearMap.toMatrix R.basis R.basis
        (G.latticeAction d'.reflection).toLinearMap =
          dihedralReflectionMatrix3IndexThree := by
      rw [G.rotateReflection_toMatrix]
      rw [R.matrix_eq]
      change B * rotationMatrix3 ^ n.val = _
      rw [hshape]
      simpa using hn
    refine ⟨d', ⟨DihedralLatticeNormalForm.ofMatrices G d' .p31m ?_
      R.basis ?_ ?_⟩⟩
    · change .three = d.order
      exact horder.symm
    · simpa [d', DihedralLatticeForm.rotationMatrix] using R.matrix_eq
    · simpa [DihedralLatticeForm.reflectionMatrix] using href

/-- After choosing the primitive member of an adjacent pair, every order-four dihedral action
has the unique joint lattice form. -/
theorem exists_orderFour_dihedralLatticeNormalForm
    (G : PlaneGroup) (d : DihedralGenerators G) (horder : d.order = .four) :
    ∃ d' : DihedralGenerators G, Nonempty (DihedralLatticeNormalForm G d') := by
  have hrorder : orderOf d.rotation.1 = 4 := by
    simpa [horder, DihedralRotationOrder.toNat] using d.rotation_order
  obtain ⟨R⟩ := G.exists_orderFour_latticeActionNormalForm d.rotation hrorder
  let B := LinearMap.toMatrix R.basis R.basis
    (G.latticeAction d.reflection).toLinearMap
  have hrel : B * rotationMatrix 0 = dihedralRotationInverseMatrix 0 * B := by
    apply G.reversing_matrix_relation d R.basis 0
    simpa [rotationMatrix4] using R.matrix_eq
  have hshape := matrix_eq_of_mul_rotationMatrix_eq_inverse_mul B 0 hrel
  have hdet : B.det = -1 :=
    G.reversing_toMatrix_det d.reflection d.reflection_reversing R.basis
  have hnorm0 := reflection_norm_equation B 0 hshape hdet
  have hnorm : B 0 0 ^ 2 + B 0 1 ^ 2 = 1 := by simpa using hnorm0
  obtain ⟨n, hn⟩ := orderFour_shape_normalization (B 0 0) (B 0 1) hnorm
  let d' := d.rotateReflection n.val
  have href : LinearMap.toMatrix R.basis R.basis
      (G.latticeAction d'.reflection).toLinearMap = dihedralReflectionMatrix4 := by
    rw [G.rotateReflection_toMatrix]
    rw [R.matrix_eq]
    change B * rotationMatrix4 ^ n.val = _
    rw [hshape]
    simpa using hn
  refine ⟨d', ⟨DihedralLatticeNormalForm.ofMatrices G d' .orderFour ?_
    R.basis ?_ ?_⟩⟩
  · change .four = d.order
    exact horder.symm
  · simpa [d', DihedralLatticeForm.rotationMatrix] using R.matrix_eq
  · simpa [DihedralLatticeForm.reflectionMatrix] using href

/-- Every order-six dihedral action has the unique joint lattice form. -/
theorem exists_orderSix_dihedralLatticeNormalForm
    (G : PlaneGroup) (d : DihedralGenerators G) (horder : d.order = .six) :
    ∃ d' : DihedralGenerators G, Nonempty (DihedralLatticeNormalForm G d') := by
  have hrorder : orderOf d.rotation.1 = 6 := by
    simpa [horder, DihedralRotationOrder.toNat] using d.rotation_order
  obtain ⟨R⟩ := G.exists_orderSix_latticeActionNormalForm d.rotation hrorder
  let B := LinearMap.toMatrix R.basis R.basis
    (G.latticeAction d.reflection).toLinearMap
  have hrel : B * rotationMatrix 1 = dihedralRotationInverseMatrix 1 * B := by
    apply G.reversing_matrix_relation d R.basis 1
    simpa [rotationMatrix6] using R.matrix_eq
  have hshape := matrix_eq_of_mul_rotationMatrix_eq_inverse_mul B 1 hrel
  have hdet : B.det = -1 :=
    G.reversing_toMatrix_det d.reflection d.reflection_reversing R.basis
  have hnorm0 := reflection_norm_equation B 1 hshape hdet
  have hnorm : B 0 0 ^ 2 + B 0 1 ^ 2 - B 0 0 * B 0 1 = 1 := by
    simpa using hnorm0
  obtain ⟨n, hn⟩ := orderSix_shape_normalization (B 0 0) (B 0 1) hnorm
  let d' := d.rotateReflection n.val
  have href : LinearMap.toMatrix R.basis R.basis
      (G.latticeAction d'.reflection).toLinearMap = dihedralReflectionMatrix6 := by
    rw [G.rotateReflection_toMatrix]
    rw [R.matrix_eq]
    change B * rotationMatrix6 ^ n.val = _
    rw [hshape]
    simpa using hn
  refine ⟨d', ⟨DihedralLatticeNormalForm.ofMatrices G d' .orderSix ?_
    R.basis ?_ ?_⟩⟩
  · change .six = d.order
    exact horder.symm
  · simpa [d', DihedralLatticeForm.rotationMatrix] using R.matrix_eq
  · simpa [DihedralLatticeForm.reflectionMatrix] using href

/-- Every multiple-reflection point group admits one of the six joint integral lattice forms. -/
theorem exists_dihedralLatticeNormalForm
    (G : PlaneGroup) (hG : PointGroupHasMultipleReflections G) :
    ∃ d : DihedralGenerators G, Nonempty (DihedralLatticeNormalForm G d) := by
  obtain ⟨d⟩ := exists_dihedralGenerators G hG
  cases horder : d.order with
  | two => exact ⟨d, G.exists_orderTwo_dihedralLatticeNormalForm d horder⟩
  | three => exact G.exists_orderThree_dihedralLatticeNormalForm d horder
  | four => exact G.exists_orderFour_dihedralLatticeNormalForm d horder
  | six => exact G.exists_orderSix_dihedralLatticeNormalForm d horder

end PlaneGroup

end


end WallpaperGroups
