import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import WallpaperGroups.Invariants.EquivalenceAction
import WallpaperGroups.Restriction.Orientation

set_option linter.style.header false

/-!
# Cyclic point-group extensions

This file contains the reusable algebra used in the no-reflection classification.  Geometrically,
a nonidentity positive plane rotation fixes only the origin.  Consequently every lift of such a
rotation has trivial power at the rotation order.  Algebraically this supplies a splitting of the
translation--point-group extension; the later comparison theorem packages compatible split
extensions through semidirect products rather than repeating coset calculations.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-! ## Fixed vectors and powers of affine lifts -/

/-- A nonidentity positive-determinant plane isometry has no nonzero fixed vector. -/
lemma positive_isometry_fixed_eq_zero
    (r : Plane ≃ₗᵢ[ℝ] Plane)
    (hr : 0 < LinearMap.det (r.toLinearEquiv : Plane →ₗ[ℝ] Plane))
    (hr_ne : r ≠ 1)
    {x : Plane} (hx : r x = x) :
    x = 0 := by
  by_contra hx_ne
  apply hr_ne
  have hone : 0 < LinearMap.det
      (((1 : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv : Plane →ₗ[ℝ] Plane)) := by
    change 0 < LinearMap.det (LinearMap.id : Plane →ₗ[ℝ] Plane)
    rw [LinearMap.det_id]
    norm_num
  apply positive_isometry_eq_of_apply_eq hr hone hx_ne
  simpa using hx

/-- A nonidentity element of the orientation-preserving point subgroup fixes only zero. -/
theorem orientationPreserving_fixed_eq_zero
    (G : PlaneGroup)
    (r : orientationPreservingPointGroup G)
    (hr_ne : r ≠ 1)
    {x : Plane}
    (hx : (r.1 : Plane ≃ₗᵢ[ℝ] Plane) x = x) :
    x = 0 := by
  apply positive_isometry_fixed_eq_zero
    (r.1 : Plane ≃ₗᵢ[ℝ] Plane)
    (orientationPreserving_det_pos G r)
  · intro hr
    apply hr_ne
    apply Subtype.ext
    apply Subtype.ext
    exact hr
  · exact hx

/-- If a power of an affine motion has trivial linear part, its translation vector is fixed by
the motion's linear part. -/
lemma translationPart_pow_fixed
    (g : EuclideanMotion Plane) (q : ℕ)
    (hq : linearPart (g ^ q) = 1) :
    linearPart g (translationPart (g ^ q)) = translationPart (g ^ q) := by
  have htranslation :
      g ^ q = translation (translationPart (g ^ q)) :=
    eq_translation_of_linearPart_eq_one hq
  have hconj : g * g ^ q * g⁻¹ = g ^ q := by
    group
  have hconj' :
      g * translation (translationPart (g ^ q)) * g⁻¹ =
        translation (translationPart (g ^ q)) := by
    calc
      g * translation (translationPart (g ^ q)) * g⁻¹ =
          g * g ^ q * g⁻¹ :=
        congrArg (fun z : EuclideanMotion Plane => g * z * g⁻¹) htranslation.symm
      _ = g ^ q := hconj
      _ = translation (translationPart (g ^ q)) := htranslation
  rw [conjugate_translation] at hconj'
  exact translation_injective hconj'

/-- If the projected point element has trivial `q`-th power, then the `q`-th power of the lift is
its pure translation part. -/
lemma lift_pow_eq_translation
    (G : Subgroup (EuclideanMotion Plane))
    (g : G) (q : ℕ)
    (hq : (pointProjection G g) ^ q = 1) :
    (g : EuclideanMotion Plane) ^ q =
      translation (translationPart ((g : EuclideanMotion Plane) ^ q)) := by
  apply eq_translation_of_linearPart_eq_one
  have hq' := congrArg
    (fun h : pointGroup G => (h : Plane ≃ₗᵢ[ℝ] Plane)) hq
  simpa only [map_pow, Subgroup.coe_pow, Subgroup.coe_one, pointProjection_coe] using hq'

/-- The translation part of such a lift power belongs to the full translation lattice. -/
lemma lift_pow_translationPart_mem
    (G : Subgroup (EuclideanMotion Plane))
    (g : G) (q : ℕ)
    (hq : (pointProjection G g) ^ q = 1) :
    translationPart ((g : EuclideanMotion Plane) ^ q) ∈ translationVectors G := by
  change translation (translationPart ((g : EuclideanMotion Plane) ^ q)) ∈ G
  rw [← lift_pow_eq_translation G g q hq]
  exact (g ^ q).property

/-- The projected point element fixes the power-translation vector of each of its lifts. -/
lemma lift_pow_translationPart_fixed
    (G : Subgroup (EuclideanMotion Plane))
    (g : G) (q : ℕ)
    (hq : (pointProjection G g) ^ q = 1) :
    (pointProjection G g : Plane ≃ₗᵢ[ℝ] Plane)
        (translationPart ((g : EuclideanMotion Plane) ^ q)) =
      translationPart ((g : EuclideanMotion Plane) ^ q) := by
  rw [pointProjection_coe]
  apply translationPart_pow_fixed
  have hq' := congrArg
    (fun h : pointGroup G => (h : Plane ≃ₗᵢ[ℝ] Plane)) hq
  simpa only [map_pow, Subgroup.coe_pow, Subgroup.coe_one, pointProjection_coe] using hq'

/-- A lift of a nonidentity positive point element has trivial `q`-th power whenever that point
element has trivial `q`-th power. -/
theorem orientationPreserving_lift_pow_eq_one
    (G : PlaneGroup)
    (r : orientationPreservingPointGroup G)
    (hr_ne : r ≠ 1)
    (g : G.carrier)
    (hg : pointProjection G.carrier g = r.1)
    (q : ℕ)
    (hrq : r.1 ^ q = 1) :
    (g : EuclideanMotion Plane) ^ q = 1 := by
  have hlinear_g : linearPart (g : EuclideanMotion Plane) =
      (r.1 : Plane ≃ₗᵢ[ℝ] Plane) := by
    simpa only [pointProjection_coe] using congrArg Subtype.val hg
  have hlinear_pow : linearPart ((g : EuclideanMotion Plane) ^ q) = 1 := by
    rw [map_pow, hlinear_g]
    exact congrArg Subtype.val hrq
  have hfixed :
      (r.1 : Plane ≃ₗᵢ[ℝ] Plane)
          (translationPart ((g : EuclideanMotion Plane) ^ q)) =
        translationPart ((g : EuclideanMotion Plane) ^ q) := by
    rw [← hlinear_g]
    exact translationPart_pow_fixed (g : EuclideanMotion Plane) q hlinear_pow
  have hzero : translationPart ((g : EuclideanMotion Plane) ^ q) = 0 :=
    orientationPreserving_fixed_eq_zero G r hr_ne hfixed
  rw [eq_translation_of_linearPart_eq_one hlinear_pow, hzero, translation_zero]

/-- Every lift of a nonidentity positive point element has trivial power at its exact point
order. -/
theorem orientationPreserving_lift_pow_orderOf_eq_one
    (G : PlaneGroup)
    (r : orientationPreservingPointGroup G)
    (hr_ne : r ≠ 1)
    (g : G.carrier)
    (hg : pointProjection G.carrier g = r.1) :
    (g : EuclideanMotion Plane) ^ orderOf r.1 = 1 := by
  exact orientationPreserving_lift_pow_eq_one G r hr_ne g hg
    (orderOf r.1) (pow_orderOf_eq_one r.1)

/-- Raw power-translation data vanish for a nonidentity rotation.  M5 will package the analogous
general finite-order datum as a quotient-valued shift class. -/
theorem orientationPreserving_lift_powerShift_eq_zero
    (G : PlaneGroup)
    (r : orientationPreservingPointGroup G)
    (hr_ne : r ≠ 1)
    (g : G.carrier)
    (hg : pointProjection G.carrier g = r.1) :
    translationPart ((g : EuclideanMotion Plane) ^ orderOf r.1) = 0 := by
  rw [orientationPreserving_lift_pow_orderOf_eq_one G r hr_ne g hg,
    translationPart_one]

/-! ## Cyclic and split extension comparison -/

/-- The homomorphism from a finite cyclic coordinate which sends `1` to `g`. -/
noncomputable def zmodPowerHom {E : Type*} [Group E]
    (n : ℕ) (g : E) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* E :=
  AddMonoidHom.toMultiplicativeLeft <|
    ZMod.lift n ⟨
      { toFun := fun z => Additive.ofMul (g ^ z)
        map_zero' := by simp
        map_add' := by
          intro a b
          exact zpow_add g a b },
      by
        apply Additive.ofMul.injective
        change g ^ (n : ℤ) = 1
        simpa only [zpow_natCast] using hg ⟩

/-- Evaluation of `zmodPowerHom` on an integer residue. -/
@[simp]
theorem zmodPowerHom_ofAdd_intCast {E : Type*} [Group E]
    (n : ℕ) (g : E) (hg : g ^ n = 1) (z : ℤ) :
    zmodPowerHom n g hg (Multiplicative.ofAdd (z : ZMod n)) = g ^ z := by
  simp [zmodPowerHom, ZMod.lift_coe]

/-- The cyclic-coordinate generator maps to the selected group element. -/
@[simp]
theorem zmodPowerHom_ofAdd_one {E : Type*} [Group E]
    (n : ℕ) (g : E) (hg : g ^ n = 1) :
    zmodPowerHom n g hg (Multiplicative.ofAdd 1) = g := by
  simpa using zmodPowerHom_ofAdd_intCast n g hg 1

/-- A finite cyclic extension splits when a lift of a quotient generator has trivial full-period
power. -/
noncomputable def cyclicSplitting
    {N E Q : Type*} [Group N] [Group E] [Group Q] [Finite Q]
    (S : GroupExtension N E Q)
    (ρ : Q) (hρ : ∀ x : Q, x ∈ Subgroup.zpowers ρ)
    (g : E) (hg_proj : S.rightHom g = ρ)
    (hg_pow : g ^ Nat.card Q = 1) : S.Splitting := by
  let coord : Multiplicative (ZMod (Nat.card Q)) ≃* Q :=
    zmodMulEquivOfGenerator hρ rfl
  let liftHom : Multiplicative (ZMod (Nat.card Q)) →* E :=
    zmodPowerHom (Nat.card Q) g hg_pow
  let s : Q →* E := liftHom.comp coord.symm.toMonoidHom
  have hcomp : S.rightHom.comp s = MonoidHom.id Q := by
    apply MonoidHom.ext
    intro x
    obtain ⟨z, rfl⟩ := hρ x
    simp [s, liftHom, coord, hg_proj]
  refine { toMonoidHom := s, rightInverse_rightHom := ?_ }
  exact DFunLike.congr_fun hcomp

/-- The cyclic splitting maps the selected quotient generator to the selected lift. -/
@[simp]
theorem cyclicSplitting_generator
    {N E Q : Type*} [Group N] [Group E] [Group Q] [Finite Q]
    (S : GroupExtension N E Q)
    (ρ : Q) (hρ : ∀ x : Q, x ∈ Subgroup.zpowers ρ)
    (g : E) (hg_proj : S.rightHom g = ρ)
    (hg_pow : g ^ Nat.card Q = 1) :
    cyclicSplitting S ρ hρ g hg_proj hg_pow ρ = g := by
  simp [cyclicSplitting]

/-- Equivariant equivalences of the kernel and quotient identify two split group extensions. -/
noncomputable def splitExtensionMulEquiv
    {N₁ E₁ Q₁ N₂ E₂ Q₂ : Type*}
    [Group N₁] [Group E₁] [Group Q₁]
    [Group N₂] [Group E₂] [Group Q₂]
    (S₁ : GroupExtension N₁ E₁ Q₁) (S₂ : GroupExtension N₂ E₂ Q₂)
    (s₁ : S₁.Splitting) (s₂ : S₂.Splitting)
    (eN : N₁ ≃* N₂) (eQ : Q₁ ≃* Q₂)
    (heq : ∀ q : Q₁, (s₁.conjAct q).trans eN = eN.trans (s₂.conjAct (eQ q))) :
    E₁ ≃* E₂ :=
  s₁.semidirectProductMulEquiv.symm |>.trans
    ((SemidirectProduct.congr eN eQ heq).trans s₂.semidirectProductMulEquiv)

/-- The split-extension equivalence carries the left endpoint through the supplied kernel
equivalence. -/
@[simp]
theorem splitExtensionMulEquiv_inl
    {N₁ E₁ Q₁ N₂ E₂ Q₂ : Type*}
    [Group N₁] [Group E₁] [Group Q₁]
    [Group N₂] [Group E₂] [Group Q₂]
    (S₁ : GroupExtension N₁ E₁ Q₁) (S₂ : GroupExtension N₂ E₂ Q₂)
    (s₁ : S₁.Splitting) (s₂ : S₂.Splitting)
    (eN : N₁ ≃* N₂) (eQ : Q₁ ≃* Q₂)
    (heq : ∀ q : Q₁, (s₁.conjAct q).trans eN = eN.trans (s₂.conjAct (eQ q)))
    (n : N₁) :
    splitExtensionMulEquiv S₁ S₂ s₁ s₂ eN eQ heq (S₁.inl n) = S₂.inl (eN n) := by
  change s₂.semidirectProductMulEquiv
    (SemidirectProduct.congr eN eQ heq
      (s₁.semidirectProductMulEquiv.symm (S₁.inl n))) = _
  rw [show s₁.semidirectProductMulEquiv.symm (S₁.inl n) =
      SemidirectProduct.inl n by
    exact s₁.semidirectProductToGroupExtensionEquiv.symm.map_inl n]
  have hsemi : SemidirectProduct.congr eN eQ heq (SemidirectProduct.inl n) =
      SemidirectProduct.inl (eN n) := by
    ext <;> simp
  rw [hsemi]
  exact s₂.semidirectProductToGroupExtensionEquiv.map_inl (eN n)

/-- The split-extension equivalence carries the right projection through the supplied quotient
equivalence. -/
@[simp]
theorem splitExtensionMulEquiv_rightHom
    {N₁ E₁ Q₁ N₂ E₂ Q₂ : Type*}
    [Group N₁] [Group E₁] [Group Q₁]
    [Group N₂] [Group E₂] [Group Q₂]
    (S₁ : GroupExtension N₁ E₁ Q₁) (S₂ : GroupExtension N₂ E₂ Q₂)
    (s₁ : S₁.Splitting) (s₂ : S₂.Splitting)
    (eN : N₁ ≃* N₂) (eQ : Q₁ ≃* Q₂)
    (heq : ∀ q : Q₁, (s₁.conjAct q).trans eN = eN.trans (s₂.conjAct (eQ q)))
    (x : E₁) :
    S₂.rightHom (splitExtensionMulEquiv S₁ S₂ s₁ s₂ eN eQ heq x) =
      eQ (S₁.rightHom x) := by
  change S₂.rightHom (s₂.semidirectProductMulEquiv
    (SemidirectProduct.congr eN eQ heq
      (s₁.semidirectProductMulEquiv.symm x))) = _
  let y := SemidirectProduct.congr eN eQ heq (s₁.semidirectProductMulEquiv.symm x)
  rw [show S₂.rightHom (s₂.semidirectProductMulEquiv y) = y.right by
    exact s₂.semidirectProductToGroupExtensionEquiv.rightHom_map y]
  rw [SemidirectProduct.congr_apply_right]
  congr 1

/-- Transport a translation-vector additive equivalence to the two extension kernels. -/
noncomputable def translationKernelEquiv (G H : PlaneGroup)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier) :
    translationSubgroup G.carrier ≃* translationSubgroup H.carrier :=
  (translationEquiv G.carrier).symm |>.trans
    ((AddEquiv.toMultiplicative eT).trans (translationEquiv H.carrier))

/-- The transported kernel equivalence acts on pure translations through the original vector
equivalence. -/
@[simp]
theorem translationKernelEquiv_translationSubgroupElement
    (G H : PlaneGroup)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (t : translationVectors G.carrier) :
    translationKernelEquiv G H eT (translationSubgroupElement G.carrier t) =
      translationSubgroupElement H.carrier (eT t) := by
  simp [translationKernelEquiv, translationEquiv]

/-- Equivariance on translation vectors is precisely equivariance of the conjugation actions on
the two extension kernels. -/
theorem translationKernelEquiv_conjAct
    (G H : PlaneGroup)
    (sG : (pointGroupExtension G.carrier).Splitting)
    (sH : (pointGroupExtension H.carrier).Splitting)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (heq : ∀ (q : pointGroup G.carrier) (t : translationVectors G.carrier),
      eT (pointAction G.carrier q t) = pointAction H.carrier (eP q) (eT t)) :
    ∀ q : pointGroup G.carrier,
      (sG.conjAct q).trans (translationKernelEquiv G H eT) =
        (translationKernelEquiv G H eT).trans (sH.conjAct (eP q)) := by
  intro q
  apply MulEquiv.ext
  intro n
  obtain ⟨t, rfl⟩ := translationSubgroupHom_surjective G.carrier n
  change translationKernelEquiv G H eT
      ((pointGroupExtension G.carrier).conjAct (sG q)
        (translationSubgroupElement G.carrier t.toAdd)) =
    (pointGroupExtension H.carrier).conjAct (sH (eP q))
      (translationKernelEquiv G H eT
        (translationSubgroupElement G.carrier t.toAdd))
  rw [pointGroupExtension_conjAct_translationSubgroupElement]
  rw [translationKernelEquiv_translationSubgroupElement]
  rw [translationKernelEquiv_translationSubgroupElement]
  rw [pointGroupExtension_conjAct_translationSubgroupElement]
  have hprojG : pointProjection G.carrier (sG q) = q := sG.rightHom_splitting q
  have hprojH : pointProjection H.carrier (sH (eP q)) = eP q :=
    sH.rightHom_splitting (eP q)
  rw [hprojG, hprojH, heq]

/-- Intertwining one cyclic generator intertwines the complete point actions. -/
theorem cyclic_action_equivariant_of_generator
    (G H : PlaneGroup)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (ρ : pointGroup G.carrier)
    (hρ : ∀ q : pointGroup G.carrier, q ∈ Subgroup.zpowers ρ)
    (hgen : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier ρ t) =
        pointAction H.carrier (eP ρ) (eT t)) :
    ∀ (q : pointGroup G.carrier) (t : translationVectors G.carrier),
      eT (pointAction G.carrier q t) =
        pointAction H.carrier (eP q) (eT t) := by
  let K : Subgroup (pointGroup G.carrier) :=
    { carrier := {q | ∀ t : translationVectors G.carrier,
          eT (pointAction G.carrier q t) =
            pointAction H.carrier (eP q) (eT t)}
      one_mem' := by intro t; simp
      mul_mem' := by
        intro a b ha hb t
        rw [pointAction_mul, map_mul, pointAction_mul, ha, hb]
      inv_mem' := by
        intro a ha t
        have h := ha (pointAction G.carrier a⁻¹ t)
        have h' := congrArg (fun u => pointAction H.carrier (eP a)⁻¹ u) h
        simpa [← pointAction_mul] using h'.symm }
  have hmem : ρ ∈ K := hgen
  have hz : Subgroup.zpowers ρ ≤ K := Subgroup.zpowers_le.mpr hmem
  intro q t
  exact hz (hρ q) t

/-- Split plane-group extensions with equivariantly identified translation and point actions are
translation-preservingly isomorphic. -/
noncomputable def splitPlaneGroupIso
    (G H : PlaneGroup)
    (sG : (pointGroupExtension G.carrier).Splitting)
    (sH : (pointGroupExtension H.carrier).Splitting)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (heq : ∀ (q : pointGroup G.carrier) (t : translationVectors G.carrier),
      eT (pointAction G.carrier q t) = pointAction H.carrier (eP q) (eT t)) :
    TranslationPreservingIso G H := by
  let eN := translationKernelEquiv G H eT
  let hact := translationKernelEquiv_conjAct G H sG sH eT eP heq
  let F := splitExtensionMulEquiv
    (pointGroupExtension G.carrier) (pointGroupExtension H.carrier)
    sG sH eN eP hact
  refine { toMulEquiv := F, map_translationSubgroup := ?_ }
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [mem_translationSubgroup]
    have hp : pointProjection H.carrier (F x) = eP (pointProjection G.carrier x) :=
      splitExtensionMulEquiv_rightHom
        (pointGroupExtension G.carrier) (pointGroupExtension H.carrier)
        sG sH eN eP hact x
    have hx' : pointProjection G.carrier x = 1 := Subtype.ext hx
    rw [hx', map_one] at hp
    exact congrArg Subtype.val hp
  · intro y hy
    let nH : translationSubgroup H.carrier := ⟨y, hy⟩
    let nG : translationSubgroup G.carrier := eN.symm nH
    refine ⟨(nG : G.carrier), nG.property, ?_⟩
    have hinl := splitExtensionMulEquiv_inl
      (pointGroupExtension G.carrier) (pointGroupExtension H.carrier)
      sG sH eN eP hact nG
    calc
      F (nG : G.carrier) = (eN nG : H.carrier) := by simpa [F] using hinl
      _ = y := by
        rw [show eN nG = nH by exact eN.apply_symm_apply nH]

/-- A cyclic point-group generator and an order-compatible lift that split the canonical
translation--point-group extension. -/
structure SplitCyclicPointExtension (G : PlaneGroup) where
  /-- Selected point-group generator. -/
  generator : pointGroup G.carrier
  /-- Every point element is an integer power of the generator. -/
  generates : ∀ q : pointGroup G.carrier, q ∈ Subgroup.zpowers generator
  /-- Selected affine lift of the generator. -/
  lift : G.carrier
  /-- The selected lift projects to the generator. -/
  lift_projection : pointProjection G.carrier lift = generator
  /-- The selected lift has trivial power at the cardinality of the point group. -/
  lift_pow_card : lift ^ Nat.card (pointGroup G.carrier) = 1

/-- Transport a stored-lattice equivalence to the actual translation-vector groups. -/
def translationVectorEquivOfLatticeEquiv
    (G H : PlaneGroup)
    (eL : G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier) :
    translationVectors G.carrier ≃+ translationVectors H.carrier :=
  G.latticeTranslationEquiv.symm |>.trans
    (eL.toAddEquiv.trans H.latticeTranslationEquiv)

/-- Intertwining a stored lattice action gives the corresponding translation-vector
intertwining identity. -/
theorem translationVectorEquivOfLatticeEquiv_intertwine
    (G H : PlaneGroup)
    (eL : G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier)
    (qG : pointGroup G.carrier) (qH : pointGroup H.carrier)
    (hL : ∀ t : G.translationLattice.carrier,
      eL (G.latticeAction qG t) = H.latticeAction qH (eL t))
    (t : translationVectors G.carrier) :
    translationVectorEquivOfLatticeEquiv G H eL
        (pointAction G.carrier qG t) =
      pointAction H.carrier qH
        (translationVectorEquivOfLatticeEquiv G H eL t) := by
  let u : G.translationLattice.carrier := G.latticeTranslationEquiv.symm t
  apply H.latticeTranslationEquiv.symm.injective
  change eL (G.latticeAction qG u) = H.latticeAction qH (eL u)
  exact hL u

/-- Reusable cyclic-extension isomorphism.  Matched cyclic generators, an equivariant
translation-vector equivalence, and full-period lifts determine a translation-preserving group
isomorphism. -/
noncomputable def cyclicExtensionIso
    (G H : PlaneGroup)
    (cG : SplitCyclicPointExtension G)
    (cH : SplitCyclicPointExtension H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (hgenerator : eP cG.generator = cH.generator)
    (hintertwine : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction H.carrier cH.generator (eT t)) :
    TranslationPreservingIso G H := by
  let sG : (pointGroupExtension G.carrier).Splitting :=
    cyclicSplitting (pointGroupExtension G.carrier)
      cG.generator cG.generates cG.lift cG.lift_projection cG.lift_pow_card
  let sH : (pointGroupExtension H.carrier).Splitting :=
    cyclicSplitting (pointGroupExtension H.carrier)
      cH.generator cH.generates cH.lift cH.lift_projection cH.lift_pow_card
  have hgen : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction H.carrier (eP cG.generator) (eT t) := by
    intro t
    rw [hgenerator]
    exact hintertwine t
  exact splitPlaneGroupIso G H sG sH eT eP
    (cyclic_action_equivariant_of_generator G H eT eP
      cG.generator cG.generates hgen)

/-- Lattice-level wrapper around `cyclicExtensionIso`, matching the normal-form interface used
by the no-reflection classification. -/
noncomputable def cyclicExtensionIsoOfLatticeEquiv
    (G H : PlaneGroup)
    (cG : SplitCyclicPointExtension G)
    (cH : SplitCyclicPointExtension H)
    (eL : G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (hgenerator : eP cG.generator = cH.generator)
    (hintertwine : ∀ t : G.translationLattice.carrier,
      eL (G.latticeAction cG.generator t) =
        H.latticeAction cH.generator (eL t)) :
    TranslationPreservingIso G H :=
  cyclicExtensionIso G H cG cH
    (translationVectorEquivOfLatticeEquiv G H eL) eP hgenerator
    (translationVectorEquivOfLatticeEquiv_intertwine G H eL
      cG.generator cH.generator hintertwine)

end

end WallpaperGroups
