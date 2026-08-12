import WallpaperGroups.Invariants.ShiftClass
import WallpaperGroups.Invariants.ReflectionFamilies
import WallpaperGroups.Presentations.DihedralExtension
import WallpaperGroups.Restriction.ReflectionNormalForms

set_option linter.style.header false

/-!
# Reflection shifts in dihedral point groups

This file turns the quotient-valued reflection shifts from M5 into the finite data used by the
multiple-reflection classification.  In the centered lattice normal form the quotient is trivial.
In the primitive form it consists exactly of the zero class and the class of the first normal-form
basis vector.  Two primitive reflection shifts therefore give a pair of bits; swapping the two
reflection generators identifies the two mixed pairs.

The order-dependent compatibility is discharged by the simultaneous lattice normal forms and
the two-reflection extension comparison.  This file therefore exports only the complete
quotient and generator-exchange invariants, not a second parameterized signature hierarchy.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-! ## Reflection quotients in the two lattice normal forms -/

/-- For an involution, the finite norm is `t + s t`. -/
@[simp]
theorem reflectionFiniteNormHom_two
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (t : translationVectors G.carrier) :
    finiteNormHom G s 2 t = t + pointAction G.carrier s t := by
  simp [finiteNormHom_apply, Finset.sum_range_succ]

/-- Pull a fixed translation vector back to the stored lattice. -/
def fixedTranslationLatticeVector
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (t : fixedTranslationSubgroup G s) : G.translationLattice.carrier :=
  G.latticeTranslationEquiv.symm (t : translationVectors G.carrier)

/-- The lattice vector underlying a fixed translation is fixed by the integral action. -/
theorem fixedTranslationLatticeVector_mem_fixed
    (G : PlaneGroup) (s : pointGroup G.carrier)
    (t : fixedTranslationSubgroup G s) :
    fixedTranslationLatticeVector G s t ∈ G.reflectionFixedSubmodule s := by
  rw [PlaneGroup.mem_reflectionFixedSubmodule_iff]
  apply G.latticeTranslationEquiv.injective
  rw [TranslationPreservingIso.latticeTranslationEquiv_latticeAction]
  change pointAction G.carrier s (t : translationVectors G.carrier) =
    (t : translationVectors G.carrier)
  exact t.property

/-- Membership in the order-two norm subgroup is the corresponding reflection-norm membership
after passing to stored lattice coordinates. -/
theorem fixedTranslation_mem_orderTwoNorm_iff
    (G : PlaneGroup) (s : pointGroup G.carrier) (hsq : s ^ 2 = 1)
    (t : fixedTranslationSubgroup G s) :
    t ∈ normTranslationSubgroup G s 2 hsq ↔
      fixedTranslationLatticeVector G s t ∈ G.reflectionNormRange s := by
  constructor
  · rintro ⟨u, hu⟩
    rw [PlaneGroup.mem_reflectionNormRange_iff]
    let uL : G.translationLattice.carrier := G.latticeTranslationEquiv.symm u
    refine ⟨uL, ?_⟩
    apply G.latticeTranslationEquiv.injective
    rw [G.latticeTranslationEquiv.map_add]
    rw [TranslationPreservingIso.latticeTranslationEquiv_latticeAction]
    rw [G.latticeTranslationEquiv.apply_symm_apply]
    change u + pointAction G.carrier s u =
      G.latticeTranslationEquiv
        (G.latticeTranslationEquiv.symm (t : translationVectors G.carrier))
    rw [G.latticeTranslationEquiv.apply_symm_apply]
    have hu' := congrArg Subtype.val hu
    change finiteNormHom G s 2 u = (t : translationVectors G.carrier) at hu'
    rw [reflectionFiniteNormHom_two] at hu'
    exact hu'
  · rw [PlaneGroup.mem_reflectionNormRange_iff]
    rintro ⟨u, hu⟩
    refine ⟨G.latticeTranslationEquiv u, ?_⟩
    apply Subtype.ext
    change finiteNormHom G s 2 (G.latticeTranslationEquiv u) =
      (t : translationVectors G.carrier)
    rw [reflectionFiniteNormHom_two]
    rw [← TranslationPreservingIso.latticeTranslationEquiv_latticeAction]
    rw [← G.latticeTranslationEquiv.map_add, hu]
    exact G.latticeTranslationEquiv.apply_symm_apply (t : translationVectors G.carrier)

/-- In a centered reflection normal form every element of the shift quotient is zero. -/
theorem centered_reflectionShiftClass_eq_zero
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .centered)
    (x : ShiftClassGroup G s 2 hsq) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
      apply (QuotientAddGroup.eq_zero_iff _).2
      rw [fixedTranslation_mem_orderTwoNorm_iff]
      exact (N.centered_mem_reflectionNormRange_iff hkind _).2
        (fixedTranslationLatticeVector_mem_fixed G s t)

/-- Consequently the shift class of every lift of a centered reflection vanishes. -/
theorem centered_reflection_shiftClass_eq_zero
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .centered)
    (g : G.carrier) (hg : pointProjection G.carrier g = s) :
    shiftClass G s 2 hsq g hg = 0 :=
  centered_reflectionShiftClass_eq_zero hsq N hkind _

/-- The fixed translation represented by the first basis vector of a primitive normal form. -/
def primitiveBasisZeroFixedTranslation
    {G : PlaneGroup} {s : pointGroup G.carrier}
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .primitive) :
    fixedTranslationSubgroup G s :=
  ⟨G.latticeTranslationEquiv (N.basis 0), by
    change pointAction G.carrier s (G.latticeTranslationEquiv (N.basis 0)) =
      G.latticeTranslationEquiv (N.basis 0)
    rw [← TranslationPreservingIso.latticeTranslationEquiv_latticeAction]
    exact congrArg G.latticeTranslationEquiv
      ((PlaneGroup.mem_reflectionFixedSubmodule_iff G s (N.basis 0)).1
        (N.primitive_basis_zero_mem_fixed hkind))⟩

/-- The canonical nonzero class in a primitive reflection quotient. -/
def primitiveBasisZeroShiftClass
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .primitive) :
    ShiftClassGroup G s 2 hsq :=
  QuotientAddGroup.mk' (normTranslationSubgroup G s 2 hsq)
    (primitiveBasisZeroFixedTranslation N hkind)

/-- The first-basis-vector class in a primitive reflection quotient is nonzero. -/
theorem primitiveBasisZeroShiftClass_ne_zero
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .primitive) :
    primitiveBasisZeroShiftClass hsq N hkind ≠ 0 := by
  intro hz
  have hmem : primitiveBasisZeroFixedTranslation N hkind ∈
      normTranslationSubgroup G s 2 hsq :=
    (QuotientAddGroup.eq_zero_iff _).1 hz
  rw [fixedTranslation_mem_orderTwoNorm_iff] at hmem
  apply N.primitive_basis_zero_not_mem_reflectionNormRange hkind
  simpa [fixedTranslationLatticeVector, primitiveBasisZeroFixedTranslation] using hmem

/-- Every primitive reflection quotient element is either zero or the first-basis-vector class. -/
theorem primitive_reflectionShiftClass_eq_zero_or_basisZero
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .primitive)
    (x : ShiftClassGroup G s 2 hsq) :
    x = 0 ∨ x = primitiveBasisZeroShiftClass hsq N hkind := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
      have htfix : fixedTranslationLatticeVector G s t ∈
          G.reflectionFixedSubmodule s :=
        fixedTranslationLatticeVector_mem_fixed G s t
      rcases N.primitive_fixed_zero_or_basis_zero_class hkind htfix with hzero | hbasis
      · left
        apply (QuotientAddGroup.eq_zero_iff _).2
        exact (fixedTranslation_mem_orderTwoNorm_iff G s hsq t).2 hzero
      · right
        apply (QuotientAddGroup.eq_iff_sub_mem).2
        rw [fixedTranslation_mem_orderTwoNorm_iff]
        simpa [fixedTranslationLatticeVector, primitiveBasisZeroFixedTranslation,
          map_sub] using hbasis

/-- In a primitive reflection quotient, vanishing is a complete invariant: two classes are
equal exactly when either both vanish or both are the unique nonzero class. -/
theorem primitive_reflectionShiftClass_eq_of_eq_zero_iff
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .primitive)
    (x y : ShiftClassGroup G s 2 hsq) (hzero : x = 0 ↔ y = 0) :
    x = y := by
  by_cases hx : x = 0
  · exact hx.trans (hzero.mp hx).symm
  · have hy : y ≠ 0 := by
      intro hy
      exact hx (hzero.mpr hy)
    rcases primitive_reflectionShiftClass_eq_zero_or_basisZero hsq N hkind x with
      hx0 | hx1
    · exact (hx hx0).elim
    · rcases primitive_reflectionShiftClass_eq_zero_or_basisZero hsq N hkind y with
        hy0 | hy1
      · exact (hy hy0).elim
      · exact hx1.trans hy1.symm

/-- A two-valued encoding of a primitive reflection shift quotient. -/
inductive ReflectionShiftBit
  | zero
  | nonzero
  deriving DecidableEq

instance : Fintype ReflectionShiftBit where
  elems := {.zero, .nonzero}
  complete b := by cases b <;> simp

/-- Encode a primitive quotient class by whether it vanishes. -/
noncomputable def primitiveReflectionShiftBit
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (_hkind : N.kind = .primitive)
    (x : ShiftClassGroup G s 2 hsq) : ReflectionShiftBit := by
  classical
  exact if x = 0 then .zero else .nonzero

/-- The primitive bit is zero exactly when the quotient class is zero. -/
@[simp]
theorem primitiveReflectionShiftBit_eq_zero_iff
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .primitive)
    (x : ShiftClassGroup G s 2 hsq) :
    primitiveReflectionShiftBit hsq N hkind x = .zero ↔ x = 0 := by
  classical
  simp [primitiveReflectionShiftBit]

/-- The primitive bit is nonzero exactly when the quotient class is nonzero. -/
@[simp]
theorem primitiveReflectionShiftBit_eq_nonzero_iff
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .primitive)
    (x : ShiftClassGroup G s 2 hsq) :
    primitiveReflectionShiftBit hsq N hkind x = .nonzero ↔ x ≠ 0 := by
  classical
  simp [primitiveReflectionShiftBit]

/-- Primitive reflection bits agree whenever the two quotient classes have the same
vanishing behavior.  The quotient groups and their normal-form bases may be unrelated; this
is the small interface used after shift-class functoriality has supplied the vanishing
equivalence. -/
theorem primitiveReflectionShiftBit_eq_of_eq_zero_iff
    {G H : PlaneGroup}
    {s : pointGroup G.carrier} {t : pointGroup H.carrier}
    (hsq : s ^ 2 = 1) (htq : t ^ 2 = 1)
    (NG : G.ReflectionLatticeNormalForm s)
    (NH : H.ReflectionLatticeNormalForm t)
    (hGkind : NG.kind = .primitive) (hHkind : NH.kind = .primitive)
    (x : ShiftClassGroup G s 2 hsq) (y : ShiftClassGroup H t 2 htq)
    (hzero : x = 0 ↔ y = 0) :
    primitiveReflectionShiftBit hsq NG hGkind x =
      primitiveReflectionShiftBit htq NH hHkind y := by
  classical
  by_cases hx : x = 0
  · have hy : y = 0 := hzero.mp hx
    simp [primitiveReflectionShiftBit, hx, hy]
  · have hy : y ≠ 0 := by
      intro hy
      exact hx (hzero.mpr hy)
    simp [primitiveReflectionShiftBit, hx, hy]

/-- Decoding the primitive bit recovers the original quotient class. -/
theorem primitiveReflectionShiftClass_eq_bitRepresentative
    {G : PlaneGroup} {s : pointGroup G.carrier} (hsq : s ^ 2 = 1)
    (N : G.ReflectionLatticeNormalForm s) (hkind : N.kind = .primitive)
    (x : ShiftClassGroup G s 2 hsq) :
    x = match primitiveReflectionShiftBit hsq N hkind x with
      | .zero => 0
      | .nonzero => primitiveBasisZeroShiftClass hsq N hkind := by
  classical
  by_cases hx : x = 0
  · simp [primitiveReflectionShiftBit, hx]
  · have hcases := primitive_reflectionShiftClass_eq_zero_or_basisZero hsq N hkind x
    rcases hcases with hzero | hbasis
    · exact (hx hzero).elim
    · simpa [primitiveReflectionShiftBit, hx] using hbasis

/-! ## Two reflection bits and generator-exchange normalization -/

/-- An ordered pair of reflection shift bits. -/
abbrev ReflectionShiftBitPair := ReflectionShiftBit × ReflectionShiftBit

/-- Exchange the two selected reflection generators. -/
def swapReflectionShiftBitPair (p : ReflectionShiftBitPair) : ReflectionShiftBitPair :=
  (p.2, p.1)

/-- The three orbits of ordered bit pairs under exchange of the two generators. -/
inductive NormalizedReflectionShiftPair
  | zeroZero
  | mixed
  | nonzeroNonzero
  deriving DecidableEq

instance : Fintype NormalizedReflectionShiftPair where
  elems := {.zeroZero, .mixed, .nonzeroNonzero}
  complete p := by cases p <;> simp

/-- Normalize an ordered pair modulo exchanging the two reflections. -/
def normalizeReflectionShiftBitPair :
    ReflectionShiftBitPair → NormalizedReflectionShiftPair
  | (.zero, .zero) => .zeroZero
  | (.zero, .nonzero) => .mixed
  | (.nonzero, .zero) => .mixed
  | (.nonzero, .nonzero) => .nonzeroNonzero

/-- Exchanging the selected reflections leaves the normalized pair unchanged. -/
@[simp]
theorem normalizeReflectionShiftBitPair_swap (p : ReflectionShiftBitPair) :
    normalizeReflectionShiftBitPair (swapReflectionShiftBitPair p) =
      normalizeReflectionShiftBitPair p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- The mixed normalized signature is precisely the orbit of `01` and `10`. -/
theorem normalizeReflectionShiftBitPair_eq_mixed_iff (p : ReflectionShiftBitPair) :
    normalizeReflectionShiftBitPair p = .mixed ↔
      p = (.zero, .nonzero) ∨ p = (.nonzero, .zero) := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> simp [normalizeReflectionShiftBitPair]

/-- Two ordered reflection-bit pairs have the same normalized signature exactly when they are
equal or differ by exchanging the selected reflection generators. -/
theorem normalizeReflectionShiftBitPair_eq_iff
    (p q : ReflectionShiftBitPair) :
    normalizeReflectionShiftBitPair p = normalizeReflectionShiftBitPair q ↔
      p = q ∨ p = swapReflectionShiftBitPair q := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [normalizeReflectionShiftBitPair, swapReflectionShiftBitPair]

/-- The four order-two signatures: one centered case and three primitive bit-pair orbits. -/
inductive QTwoReflectionShiftSignature
  | centered
  | primitive (pair : NormalizedReflectionShiftPair)
  deriving DecidableEq, Fintype

/-! ## Shift classes selected by dihedral extension data -/

namespace DihedralExtensionData

variable {G : PlaneGroup}

/-- The second standard reflection is the first reflection followed by the rotation generator. -/
def secondReflectionGenerator (c : DihedralExtensionData G) : pointGroup G.carrier :=
  c.reflectionGenerator * c.rotationGenerator

/-- The second standard reflection is an involution. -/
theorem secondReflection_sq (c : DihedralExtensionData G) :
    c.secondReflectionGenerator ^ 2 = 1 := by
  have hinv : c.reflectionGenerator⁻¹ = c.reflectionGenerator := by
    rw [inv_eq_iff_mul_eq_one]
    simpa [pow_two] using c.reflection_sq
  have hconj := c.reflection_conjugates
    ⟨c.rotationGenerator, Subgroup.mem_zpowers c.rotationGenerator⟩
  rw [hinv] at hconj
  change (c.reflectionGenerator * c.rotationGenerator) ^ 2 = 1
  rw [pow_two]
  calc
    c.reflectionGenerator * c.rotationGenerator *
          (c.reflectionGenerator * c.rotationGenerator) =
        (c.reflectionGenerator * c.rotationGenerator * c.reflectionGenerator) *
          c.rotationGenerator := by group
    _ = c.rotationGenerator⁻¹ * c.rotationGenerator := by rw [hconj]
    _ = 1 := by simp

/-- The quotient-valued shift of the selected first reflection lift. -/
def firstReflectionShiftClass (c : DihedralExtensionData G) :
    ShiftClassGroup G c.reflectionGenerator 2 c.reflection_sq :=
  shiftClass G c.reflectionGenerator 2 c.reflection_sq
    (c.lift c.reflectionGenerator) (c.lift_projection c.reflectionGenerator)

/-- The quotient-valued shift of the selected second reflection lift. -/
def secondReflectionShiftClass (c : DihedralExtensionData G) :
    ShiftClassGroup G c.secondReflectionGenerator 2 c.secondReflection_sq :=
  shiftClass G c.secondReflectionGenerator 2 c.secondReflection_sq
    (c.lift c.secondReflectionGenerator) (c.lift_projection c.secondReflectionGenerator)

/-- The ordered pair of primitive shift bits for the two standard reflections. -/
noncomputable def primitiveReflectionShiftBitPair
    (c : DihedralExtensionData G)
    (N₀ : G.ReflectionLatticeNormalForm c.reflectionGenerator)
    (N₁ : G.ReflectionLatticeNormalForm c.secondReflectionGenerator)
    (h₀ : N₀.kind = .primitive) (h₁ : N₁.kind = .primitive) :
    ReflectionShiftBitPair :=
  (primitiveReflectionShiftBit c.reflection_sq N₀ h₀ c.firstReflectionShiftClass,
    primitiveReflectionShiftBit c.secondReflection_sq N₁ h₁ c.secondReflectionShiftClass)

/-- The order-two primitive signature, normalized under exchange of the two reflection
generators. -/
noncomputable def qTwoPrimitiveShiftSignature
    (c : DihedralExtensionData G)
    (N₀ : G.ReflectionLatticeNormalForm c.reflectionGenerator)
    (N₁ : G.ReflectionLatticeNormalForm c.secondReflectionGenerator)
    (h₀ : N₀.kind = .primitive) (h₁ : N₁.kind = .primitive) :
    QTwoReflectionShiftSignature :=
  .primitive (normalizeReflectionShiftBitPair
    (c.primitiveReflectionShiftBitPair N₀ N₁ h₀ h₁))

end DihedralExtensionData

/-! ## Conjugacy invariance -/

/-- Inner conjugation carries vanishing of a reflection shift class to any conjugate reflection.
The statement is independent of both selected lifts. -/
theorem reflectionShiftClass_eq_zero_iff_inner
    (G : PlaneGroup) (a : G.carrier)
    (h k : pointGroup G.carrier)
    (hconj : pointProjection G.carrier a * h *
      (pointProjection G.carrier a)⁻¹ = k)
    (hh : h ^ 2 = 1) (hk : k ^ 2 = 1)
    (x : G.carrier) (hx : pointProjection G.carrier x = h)
    (y : G.carrier) (hy : pointProjection G.carrier y = k) :
    shiftClass G h 2 hh x hx = 0 ↔
      shiftClass G k 2 hk y hy = 0 := by
  let e := TranslationPreservingIso.inner G a
  have hmap : e.pointGroupEquiv h = k := by
    simpa [e] using hconj
  have hnatural := shiftClass_eq_zero_iff_map e h 2 hh x hx
  have hproj : pointProjection G.carrier (e.toMulEquiv x) = k :=
    (mappedLiftProjection e h x hx).trans hmap
  have htransport :
      shiftClass G (e.pointGroupEquiv h) 2
          (transportedPointPowerProof e h 2 hh)
          (e.toMulEquiv x) (mappedLiftProjection e h x hx) = 0 ↔
        shiftClass G k 2 hk (e.toMulEquiv x) hproj = 0 :=
    shiftClass_eq_zero_congr_point hmap 2
      (transportedPointPowerProof e h 2 hh) hk (e.toMulEquiv x)
      (mappedLiftProjection e h x hx) hproj
  have hind := shiftClass_lift_independent G k 2 hk
    (e.toMulEquiv x) y hproj hy
  constructor
  · intro hz
    have hmapped := hnatural.mp hz
    have hmapped' := htransport.mp hmapped
    rw [hind] at hmapped'
    exact hmapped'
  · intro hz
    apply hnatural.mpr
    apply htransport.mpr
    rw [hind]
    exact hz

end

end WallpaperGroups
