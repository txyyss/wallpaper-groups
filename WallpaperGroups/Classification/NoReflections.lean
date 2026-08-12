import WallpaperGroups.Models.RotationModels
import WallpaperGroups.Presentations.CyclicExtension
import WallpaperGroups.Restriction.LatticeNormalForms

set_option linter.style.header false

/-!
# Classification without reflections

This file proves the `p1`, `p2`, `p3`, `p4`, and `p6` slice of the wallpaper-group
classification.  A point group has no reflections precisely when every point element has positive
determinant.  Its cyclic extension splits because rotation power shifts vanish, and the lattice
action normal forms from M3 identify groups having the same rotation order.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-- A point group has no reflections when all of its elements preserve orientation. -/
def PointGroupHasNoReflections (G : PlaneGroup) : Prop :=
  ∀ p : pointGroup G.carrier, p ∈ orientationPreservingPointGroup G

/-- A no-reflection point group is cyclic. -/
theorem pointGroup_isCyclic_of_noReflections
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    IsCyclic (pointGroup G.carrier) :=
  pointGroup_isCyclic_of_all_orientationPreserving G hG

/-- A no-reflection point group has a cyclic generator. -/
theorem exists_pointGenerator_of_noReflections
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    ∃ ρ : pointGroup G.carrier,
      ∀ q : pointGroup G.carrier, q ∈ Subgroup.zpowers ρ := by
  let _ : IsCyclic (pointGroup G.carrier) :=
    pointGroup_isCyclic_of_noReflections G hG
  exact IsCyclic.exists_generator

/-- A finite point-group generator has order equal to the point-group cardinality. -/
theorem pointGenerator_order_eq_card
    (G : PlaneGroup) (ρ : pointGroup G.carrier)
    (hρ : ∀ q : pointGroup G.carrier, q ∈ Subgroup.zpowers ρ) :
    orderOf ρ = Nat.card (pointGroup G.carrier) :=
  orderOf_eq_card_of_forall_mem_zpowers hρ

/-- A finite point-group generator is trivial exactly when the point group has cardinality one. -/
theorem pointGenerator_eq_one_iff_card_eq_one
    (G : PlaneGroup) (ρ : pointGroup G.carrier)
    (hρ : ∀ q : pointGroup G.carrier, q ∈ Subgroup.zpowers ρ) :
    ρ = 1 ↔ Nat.card (pointGroup G.carrier) = 1 := by
  rw [← orderOf_eq_one_iff, pointGenerator_order_eq_card G ρ hρ]

/-- Under the no-reflection hypothesis, a point generator has crystallographic order. -/
theorem pointGenerator_order_isCrystallographic
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G)
    (ρ : pointGroup G.carrier)
    (_hρ : ∀ q : pointGroup G.carrier, q ∈ Subgroup.zpowers ρ) :
    IsCrystallographicOrder (orderOf ρ) := by
  let r : orientationPreservingPointGroup G := ⟨ρ, hG ρ⟩
  exact G.orientationPreserving_order_isCrystallographic r

/-- The cardinality of a no-reflection point group is one of `1, 2, 3, 4, 6`. -/
theorem noReflections_pointGroup_card_isCrystallographic
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    IsCrystallographicOrder (Nat.card (pointGroup G.carrier)) := by
  obtain ⟨ρ, hρ⟩ := exists_pointGenerator_of_noReflections G hG
  rw [← pointGenerator_order_eq_card G ρ hρ]
  exact pointGenerator_order_isCrystallographic G hG ρ hρ

/-- Typed cardinality form of the crystallographic restriction in the no-reflection case. -/
theorem noReflections_pointGroup_card_eq_toNat
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    ∃ q : CrystallographicOrder,
      Nat.card (pointGroup G.carrier) = q.toNat :=
  (isCrystallographicOrder_iff_exists_toNat
    (Nat.card (pointGroup G.carrier))).mp
      (noReflections_pointGroup_card_isCrystallographic G hG)

namespace CrystallographicOrder

/-- Distinct crystallographic-order constructors have distinct natural-number values. -/
theorem toNat_injective : Function.Injective toNat := by
  intro q r h
  cases q <;> cases r <;> simp_all [toNat]

end CrystallographicOrder

/-- The canonical five-valued signature of a no-reflection plane group. -/
noncomputable def noReflectionSignature
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    CrystallographicOrder :=
  Classical.choose (noReflections_pointGroup_card_eq_toNat G hG)

/-- The natural value of the no-reflection signature is the point-group cardinality. -/
@[simp]
theorem noReflectionSignature_card
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    Nat.card (pointGroup G.carrier) = (noReflectionSignature G hG).toNat :=
  Classical.choose_spec (noReflections_pointGroup_card_eq_toNat G hG)

/-- Translation-preserving equivalence preserves the five-valued no-reflection signature. -/
theorem noReflectionSignature_eq_of_iso
    {G H : PlaneGroup}
    (hG : PointGroupHasNoReflections G)
    (hH : PointGroupHasNoReflections H)
    (e : TranslationPreservingIso G H) :
    noReflectionSignature G hG = noReflectionSignature H hH := by
  apply CrystallographicOrder.toNat_injective
  rw [← noReflectionSignature_card G hG, ← noReflectionSignature_card H hH]
  exact e.pointGroup_natCard_eq

/-- Different no-reflection signatures obstruct translation-preserving equivalence. -/
theorem not_equivalent_of_noReflectionSignature_ne
    {G H : PlaneGroup}
    (hG : PointGroupHasNoReflections G)
    (hH : PointGroupHasNoReflections H)
    (hne : noReflectionSignature G hG ≠ noReflectionSignature H hH) :
    ¬ PlaneGroup.Equivalent G H := by
  rintro ⟨e⟩
  exact hne (noReflectionSignature_eq_of_iso hG hH e)

/-- A no-reflection plane group has cyclic splitting data.  In the trivial case the lift is the
identity; otherwise every lift of the selected generator has trivial full-period power. -/
noncomputable def splitCyclicPointExtensionOfNoReflections
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    SplitCyclicPointExtension G := by
  let ρ : pointGroup G.carrier :=
    Classical.choose (exists_pointGenerator_of_noReflections G hG)
  have hρ : ∀ q : pointGroup G.carrier, q ∈ Subgroup.zpowers ρ :=
    Classical.choose_spec (exists_pointGenerator_of_noReflections G hG)
  by_cases hρone : ρ = 1
  · exact
      { generator := ρ
        generates := hρ
        lift := 1
        lift_projection := by simp [hρone]
        lift_pow_card := by simp }
  · let r : orientationPreservingPointGroup G := ⟨ρ, hG ρ⟩
    let g : G.carrier := Classical.choose (pointProjection_surjective G.carrier ρ)
    have hg : pointProjection G.carrier g = ρ :=
      Classical.choose_spec (pointProjection_surjective G.carrier ρ)
    refine
      { generator := ρ
        generates := hρ
        lift := g
        lift_projection := hg
        lift_pow_card := ?_ }
    have hr_ne : r ≠ 1 := by
      intro hr
      apply hρone
      exact congrArg Subtype.val hr
    have hp := orientationPreserving_lift_pow_orderOf_eq_one G r hr_ne g hg
    apply Subtype.ext
    rw [← pointGenerator_order_eq_card G ρ hρ]
    exact hp

/-- The generator stored by the no-reflection split data has full point-group order. -/
theorem noReflections_split_generator_order_eq_card
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    orderOf (splitCyclicPointExtensionOfNoReflections G hG).generator =
      Nat.card (pointGroup G.carrier) :=
  pointGenerator_order_eq_card G _
    (splitCyclicPointExtensionOfNoReflections G hG).generates

/-- The stored split generator is trivial exactly in the cardinality-one case. -/
theorem noReflections_split_generator_eq_one_iff_card_eq_one
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    (splitCyclicPointExtensionOfNoReflections G hG).generator = 1 ↔
      Nat.card (pointGroup G.carrier) = 1 :=
  pointGenerator_eq_one_iff_card_eq_one G _
    (splitCyclicPointExtensionOfNoReflections G hG).generates

/-- The stored split generator has one of the five crystallographic orders. -/
theorem noReflections_split_generator_order_isCrystallographic
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    IsCrystallographicOrder
      (orderOf (splitCyclicPointExtensionOfNoReflections G hG).generator) :=
  pointGenerator_order_isCrystallographic G hG _
    (splitCyclicPointExtensionOfNoReflections G hG).generates

/-! ## Coordinate-preserving equivalences between two normal-form bases -/

/-- The integer-linear equivalence which preserves coordinates in two selected `Fin 2` bases. -/
def basisLinearEquiv
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (bM : Module.Basis (Fin 2) ℤ M)
    (bN : Module.Basis (Fin 2) ℤ N) : M ≃ₗ[ℤ] N :=
  bM.repr.trans bN.repr.symm

/-- The coordinate-preserving equivalence sends source basis vectors to target basis vectors. -/
@[simp]
theorem basisLinearEquiv_apply_basis
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (bM : Module.Basis (Fin 2) ℤ M)
    (bN : Module.Basis (Fin 2) ℤ N) (i : Fin 2) :
    basisLinearEquiv bM bN (bM i) = bN i := by
  change bN.repr.symm (bM.repr (bM i)) = bN i
  rw [bM.repr_self]
  exact bN.repr_symm_single_one i

/-- Equal action matrices in selected bases make the coordinate-preserving lattice equivalence
intertwine the two actions. -/
theorem basisLinearEquiv_intertwine
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (bM : Module.Basis (Fin 2) ℤ M)
    (bN : Module.Basis (Fin 2) ℤ N)
    (A : M ≃ₗ[ℤ] M) (B : N ≃ₗ[ℤ] N)
    (hmat : LinearMap.toMatrix bM bM A.toLinearMap =
      LinearMap.toMatrix bN bN B.toLinearMap) (x : M) :
    basisLinearEquiv bM bN (A x) = B (basisLinearEquiv bM bN x) := by
  let e := basisLinearEquiv bM bN
  have hmaps : e.toLinearMap.comp A.toLinearMap =
      B.toLinearMap.comp e.toLinearMap := by
    apply bM.ext
    intro i
    change e (A (bM i)) = B (e (bM i))
    rw [show e (bM i) = bN i by
      exact basisLinearEquiv_apply_basis bM bN i]
    apply bN.repr.injective
    ext j
    have hentry := congrFun (congrFun hmat j) i
    simpa [e, basisLinearEquiv, LinearMap.toMatrix_apply] using hentry
  exact LinearMap.congr_fun hmaps x

/-! ## Five lattice-action normal forms -/

/-- The selected-basis integral matrix for each reflection-free rotation order. -/
def noReflectionRotationMatrix :
    CrystallographicOrder → Matrix (Fin 2) (Fin 2) ℤ
  | .one => 1
  | .two => -1
  | .three => rotationMatrix3
  | .four => rotationMatrix4
  | .six => rotationMatrix6

/-- A selected lattice basis in which the canonical cyclic generator has the standard matrix for
the given crystallographic order. -/
structure NoReflectionLatticeNormalForm
    (G : PlaneGroup) (c : SplitCyclicPointExtension G)
    (q : CrystallographicOrder) where
  /-- Selected integral lattice basis. -/
  basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier
  /-- Matrix of the cyclic generator in the selected basis. -/
  matrix_eq :
    LinearMap.toMatrix basis basis (G.latticeAction c.generator).toLinearMap =
      noReflectionRotationMatrix q

/-- An order-two orientation-preserving point element acts by negation on the full lattice. -/
theorem latticeAction_eq_neg_of_order_two
    (G : PlaneGroup) (r : orientationPreservingPointGroup G)
    (hr : orderOf r.1 = 2) (t : G.translationLattice.carrier) :
    G.latticeAction r.1 t = -t := by
  have ht : (G.latticeActionMatrix r.1).trace = -2 := by
    rcases G.orientationPreserving_trace_order_cases r with
      ⟨htrace, horder⟩ | ⟨htrace, horder⟩ | ⟨htrace, horder⟩ |
      ⟨htrace, horder⟩ | ⟨htrace, horder⟩
    all_goals omega
  have htR : LinearMap.trace ℝ Plane
      (r.1 : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv.toLinearMap = -2 := by
    rw [← G.trace_cast r.1]
    exact_mod_cast ht
  have hneg := eq_neg_of_trace_eq_neg_two
    (r.1 : Plane ≃ₗᵢ[ℝ] Plane) htR
  apply Subtype.ext
  rw [G.latticeAction_coe]
  change (r.1 : Plane ≃ₗᵢ[ℝ] Plane) (t : Plane) = -(t : Plane)
  rw [hneg]
  rfl

/-- In every no-reflection case, the canonical split generator has the corresponding standard
lattice-action matrix. -/
theorem exists_noReflectionLatticeNormalForm
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G)
    (q : CrystallographicOrder)
    (hq : Nat.card (pointGroup G.carrier) = q.toNat) :
    Nonempty (NoReflectionLatticeNormalForm G
      (splitCyclicPointExtensionOfNoReflections G hG) q) := by
  let c := splitCyclicPointExtensionOfNoReflections G hG
  have horder : orderOf c.generator = q.toNat := by
    rw [noReflections_split_generator_order_eq_card G hG, hq]
  let r : orientationPreservingPointGroup G := ⟨c.generator, hG c.generator⟩
  cases q with
  | one =>
      have hgen : c.generator = 1 := orderOf_eq_one_iff.mp horder
      refine ⟨⟨G.chosenBasis, ?_⟩⟩
      change LinearMap.toMatrix G.chosenBasis G.chosenBasis
        (G.latticeAction c.generator).toLinearMap = _
      rw [hgen, G.latticeAction_one]
      simp [noReflectionRotationMatrix]
  | two =>
      refine ⟨⟨G.chosenBasis, ?_⟩⟩
      ext i j
      rw [LinearMap.toMatrix_apply]
      have hact := latticeAction_eq_neg_of_order_two G r horder
        (G.chosenBasis j)
      change G.chosenBasis.repr (G.latticeAction c.generator (G.chosenBasis j)) i = _
      rw [hact]
      by_cases hij : i = j
      · subst i
        simp [noReflectionRotationMatrix]
      · simp [noReflectionRotationMatrix, hij]
  | three =>
      obtain ⟨nf⟩ := G.exists_orderThree_latticeActionNormalForm r horder
      exact ⟨⟨nf.basis, by simpa [noReflectionRotationMatrix] using nf.matrix_eq⟩⟩
  | four =>
      obtain ⟨nf⟩ := G.exists_orderFour_latticeActionNormalForm r horder
      exact ⟨⟨nf.basis, by simpa [noReflectionRotationMatrix] using nf.matrix_eq⟩⟩
  | six =>
      obtain ⟨nf⟩ := G.exists_orderSix_latticeActionNormalForm r horder
      exact ⟨⟨nf.basis, by simpa [noReflectionRotationMatrix] using nf.matrix_eq⟩⟩

/-- The generator-preserving point-group equivalence between two finite cyclic groups of equal
cardinality. -/
noncomputable def pointGeneratorEquiv
    (G H : PlaneGroup)
    (cG : SplitCyclicPointExtension G)
    (cH : SplitCyclicPointExtension H)
    (hcard : Nat.card (pointGroup G.carrier) =
      Nat.card (pointGroup H.carrier)) :
    pointGroup G.carrier ≃* pointGroup H.carrier :=
  (zmodMulEquivOfGenerator cG.generates rfl).symm.trans
    ((AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv).trans
      (zmodMulEquivOfGenerator cH.generates rfl))

/-- The generator-preserving point equivalence sends the selected source generator to the
selected target generator. -/
theorem pointGeneratorEquiv_generator
    (G H : PlaneGroup)
    (cG : SplitCyclicPointExtension G)
    (cH : SplitCyclicPointExtension H)
    (hcard : Nat.card (pointGroup G.carrier) =
      Nat.card (pointGroup H.carrier)) :
    pointGeneratorEquiv G H cG cH hcard cG.generator = cH.generator := by
  simp [pointGeneratorEquiv]

/-- Two no-reflection plane groups with equal point-group order are equivalent. -/
theorem equivalent_of_noReflections_of_pointGroup_card_eq
    (G H : PlaneGroup)
    (hG : PointGroupHasNoReflections G)
    (hH : PointGroupHasNoReflections H)
    (hcard : Nat.card (pointGroup G.carrier) =
      Nat.card (pointGroup H.carrier)) :
    PlaneGroup.Equivalent G H := by
  let cG := splitCyclicPointExtensionOfNoReflections G hG
  let cH := splitCyclicPointExtensionOfNoReflections H hH
  obtain ⟨q, hqG⟩ := noReflections_pointGroup_card_eq_toNat G hG
  have hqH : Nat.card (pointGroup H.carrier) = q.toNat := hcard.symm.trans hqG
  obtain ⟨nfG⟩ := exists_noReflectionLatticeNormalForm G hG q hqG
  obtain ⟨nfH⟩ := exists_noReflectionLatticeNormalForm H hH q hqH
  let eL : G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier :=
    basisLinearEquiv nfG.basis nfH.basis
  let eP : pointGroup G.carrier ≃* pointGroup H.carrier :=
    pointGeneratorEquiv G H cG cH hcard
  refine ⟨cyclicExtensionIsoOfLatticeEquiv G H cG cH eL eP ?_ ?_⟩
  · exact pointGeneratorEquiv_generator G H cG cH hcard
  · intro t
    apply basisLinearEquiv_intertwine nfG.basis nfH.basis
    exact nfG.matrix_eq.trans nfH.matrix_eq.symm

/-- Two no-reflection plane groups are equivalent exactly when their five-valued signatures
agree. -/
theorem equivalent_noReflections_iff_signature_eq
    (G H : PlaneGroup)
    (hG : PointGroupHasNoReflections G)
    (hH : PointGroupHasNoReflections H) :
    PlaneGroup.Equivalent G H ↔
      noReflectionSignature G hG = noReflectionSignature H hH := by
  constructor
  · rintro ⟨e⟩
    exact noReflectionSignature_eq_of_iso hG hH e
  · intro hsig
    apply equivalent_of_noReflections_of_pointGroup_card_eq G H hG hH
    rw [noReflectionSignature_card G hG,
      noReflectionSignature_card H hH, hsig]

/-- Equivalent plane groups have equal point-group cardinality; hence no two distinct rotation
orders can be equivalent. -/
theorem not_equivalent_of_pointGroup_card_ne
    (G H : PlaneGroup)
    (hcard : Nat.card (pointGroup G.carrier) ≠
      Nat.card (pointGroup H.carrier)) :
    ¬ PlaneGroup.Equivalent G H := by
  rintro ⟨e⟩
  exact hcard e.pointGroup_natCard_eq

/-! ## Classification by the five standard rotation models -/

/-- Every standard rotation model has no orientation-reversing point-group elements. -/
theorem rotationModel_hasNoReflections (q : CrystallographicOrder) :
    PointGroupHasNoReflections (rotationModel q) :=
  rotationModel_all_orientationPreserving q

/-- The no-reflection signature of a standard rotation model is its indexing order. -/
@[simp]
theorem rotationModel_signature (q : CrystallographicOrder) :
    noReflectionSignature (rotationModel q)
      (rotationModel_hasNoReflections q) = q := by
  apply CrystallographicOrder.toNat_injective
  rw [← noReflectionSignature_card (rotationModel q)
    (rotationModel_hasNoReflections q)]
  exact rotationModel_pointGroup_card q

/-- Two standard rotation models are equivalent exactly when their rotation orders agree. -/
theorem rotationModels_equivalent_iff
    (q r : CrystallographicOrder) :
    PlaneGroup.Equivalent (rotationModel q) (rotationModel r) ↔ q = r := by
  constructor
  · rintro ⟨e⟩
    apply CrystallographicOrder.toNat_injective
    rw [← rotationModel_pointGroup_card q, ← rotationModel_pointGroup_card r]
    exact e.pointGroup_natCard_eq
  · rintro rfl
    exact PlaneGroup.Equivalent.refl (rotationModel q)

/-- Every no-reflection plane group is equivalent to a unique standard rotation model. -/
theorem classify_no_reflections
    (G : PlaneGroup) (hG : PointGroupHasNoReflections G) :
    ∃! q : CrystallographicOrder,
      PlaneGroup.Equivalent G (rotationModel q) := by
  let q := noReflectionSignature G hG
  refine ⟨q, ?_, ?_⟩
  · apply equivalent_of_noReflections_of_pointGroup_card_eq G (rotationModel q)
      hG (rotationModel_hasNoReflections q)
    rw [noReflectionSignature_card G hG, rotationModel_pointGroup_card]
  · intro r hr
    apply CrystallographicOrder.toNat_injective
    rw [← rotationModel_pointGroup_card r,
      ← noReflectionSignature_card G hG]
    exact (Classical.choice hr).pointGroup_natCard_eq.symm

end

end WallpaperGroups
