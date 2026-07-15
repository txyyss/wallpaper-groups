import WallpaperGroups.Presentations.CyclicExtension

set_option linter.style.header false

/-!
# Reflection point-group extensions

An extension by a point group with one nonidentity reflection has a unique two-coset normal
form.  This file packages that normal form and proves a reusable translation-preserving
isomorphism theorem.  The square of a selected reflection lift is the only extra relation; changing
the lift changes this square shift by the order-two norm vector.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-- Presentation data for an extension whose quotient consists of the identity and one
reflection. -/
structure ReflectionExtensionData (G : PlaneGroup) where
  generator : pointGroup G.carrier
  generator_ne_one : generator ≠ 1
  generator_cases : ∀ q : pointGroup G.carrier, q = 1 ∨ q = generator
  lift : G.carrier
  lift_projection : pointProjection G.carrier lift = generator
  shift : translationVectors G.carrier
  lift_sq : lift ^ 2 = translationElement G.carrier shift

/-- Decode translation/reflection normal-form coordinates. -/
def reflectionDecode {G : PlaneGroup} (c : ReflectionExtensionData G) :
    translationVectors G.carrier × Bool → G.carrier
  | (t, false) => translationElement G.carrier t
  | (t, true) => translationElement G.carrier t * c.lift

@[simp]
theorem pointProjection_translationElement (G : PlaneGroup)
    (t : translationVectors G.carrier) :
    pointProjection G.carrier (translationElement G.carrier t) = 1 := by
  apply Subtype.ext
  rw [pointProjection_coe]
  exact linearPart_translation _

theorem reflectionDecode_surjective {G : PlaneGroup}
    (c : ReflectionExtensionData G) : Function.Surjective (reflectionDecode c) := by
  intro x
  rcases c.generator_cases (pointProjection G.carrier x) with hx | hx
  · have hxker : x ∈ translationSubgroup G.carrier := by
      rw [← pointProjection_ker]
      exact hx
    obtain ⟨t, ht⟩ :=
      (mem_translationSubgroup_iff_exists G.carrier x).mp hxker
    refine ⟨(t, false), ?_⟩
    apply Subtype.ext
    exact ht.symm
  · let y : G.carrier := x * c.lift⁻¹
    have hyproj : pointProjection G.carrier y = 1 := by
      simp [y, hx, c.lift_projection]
    have hyker : y ∈ translationSubgroup G.carrier := by
      rw [← pointProjection_ker]
      exact hyproj
    obtain ⟨t, ht⟩ :=
      (mem_translationSubgroup_iff_exists G.carrier y).mp hyker
    have hyt : y = translationElement G.carrier t := by
      apply Subtype.ext
      exact ht
    refine ⟨(t, true), ?_⟩
    change translationElement G.carrier t * c.lift = x
    rw [← hyt]
    simp [y]

theorem reflectionDecode_injective {G : PlaneGroup}
    (c : ReflectionExtensionData G) : Function.Injective (reflectionDecode c) := by
  rintro ⟨t, b⟩ ⟨u, d⟩ h
  cases b <;> cases d
  · have htu : t = u := by
      apply Subtype.ext
      apply translation_injective
      exact congrArg (fun z : G.carrier => (z : EuclideanMotion Plane)) h
    simp [htu]
  · exfalso
    have hp := congrArg (pointProjection G.carrier) h
    simp only [reflectionDecode, map_mul, pointProjection_translationElement,
      c.lift_projection, one_mul] at hp
    exact c.generator_ne_one hp.symm
  · exfalso
    have hp := congrArg (pointProjection G.carrier) h
    simp only [reflectionDecode, map_mul, pointProjection_translationElement,
      c.lift_projection, one_mul] at hp
    exact c.generator_ne_one hp
  · have htrans : translationElement G.carrier t =
        translationElement G.carrier u := by
      exact mul_right_cancel h
    have htu : t = u := by
      apply Subtype.ext
      apply translation_injective
      exact congrArg (fun z : G.carrier => (z : EuclideanMotion Plane)) htrans
    simp [htu]

/-- Every element has unique translation/reflection normal-form coordinates. -/
noncomputable def reflectionDecodeEquiv {G : PlaneGroup}
    (c : ReflectionExtensionData G) :
    translationVectors G.carrier × Bool ≃ G.carrier :=
  Equiv.ofBijective (reflectionDecode c)
    ⟨reflectionDecode_injective c, reflectionDecode_surjective c⟩

/-- Move a translation past the selected reflection lift. -/
theorem reflectionLift_mul_translation {G : PlaneGroup}
    (c : ReflectionExtensionData G) (t : translationVectors G.carrier) :
    c.lift * translationElement G.carrier t =
      translationElement G.carrier
        (pointAction G.carrier c.generator t) * c.lift := by
  calc
    c.lift * translationElement G.carrier t =
        (c.lift * translationElement G.carrier t * c.lift⁻¹) * c.lift := by group
    _ = translationElement G.carrier
        (pointAction G.carrier (pointProjection G.carrier c.lift) t) * c.lift := by
      rw [conjugate_translationElement]
    _ = translationElement G.carrier
        (pointAction G.carrier c.generator t) * c.lift := by
      rw [c.lift_projection]

theorem reflectionDecode_mul_ff {G : PlaneGroup}
    (c : ReflectionExtensionData G) (t u : translationVectors G.carrier) :
    reflectionDecode c (t, false) * reflectionDecode c (u, false) =
      reflectionDecode c (t + u, false) := by
  exact (translationElement_add G.carrier t u).symm

theorem reflectionDecode_mul_ft {G : PlaneGroup}
    (c : ReflectionExtensionData G) (t u : translationVectors G.carrier) :
    reflectionDecode c (t, false) * reflectionDecode c (u, true) =
      reflectionDecode c (t + u, true) := by
  change translationElement G.carrier t *
      (translationElement G.carrier u * c.lift) =
    translationElement G.carrier (t + u) * c.lift
  rw [← mul_assoc, translationElement_add]

theorem reflectionDecode_mul_tf {G : PlaneGroup}
    (c : ReflectionExtensionData G) (t u : translationVectors G.carrier) :
    reflectionDecode c (t, true) * reflectionDecode c (u, false) =
      reflectionDecode c
        (t + pointAction G.carrier c.generator u, true) := by
  change (translationElement G.carrier t * c.lift) *
      translationElement G.carrier u =
    translationElement G.carrier
      (t + pointAction G.carrier c.generator u) * c.lift
  rw [mul_assoc, reflectionLift_mul_translation, ← mul_assoc,
    translationElement_add]

theorem reflectionDecode_mul_tt {G : PlaneGroup}
    (c : ReflectionExtensionData G) (t u : translationVectors G.carrier) :
    reflectionDecode c (t, true) * reflectionDecode c (u, true) =
      reflectionDecode c
        (t + pointAction G.carrier c.generator u + c.shift, false) := by
  change (translationElement G.carrier t * c.lift) *
      (translationElement G.carrier u * c.lift) =
    translationElement G.carrier
      (t + pointAction G.carrier c.generator u + c.shift)
  calc
    (translationElement G.carrier t * c.lift) *
        (translationElement G.carrier u * c.lift) =
      (translationElement G.carrier t *
        (c.lift * translationElement G.carrier u)) * c.lift := by group
    _ = (translationElement G.carrier t *
        (translationElement G.carrier
          (pointAction G.carrier c.generator u) * c.lift)) * c.lift := by
          rw [reflectionLift_mul_translation]
    _ = (translationElement G.carrier t *
        translationElement G.carrier
          (pointAction G.carrier c.generator u)) *
        (c.lift * c.lift) := by group
    _ = translationElement G.carrier
          (t + pointAction G.carrier c.generator u) *
        translationElement G.carrier c.shift := by
          rw [← translationElement_add]
          rw [show c.lift * c.lift = c.lift ^ 2 by simp [pow_two], c.lift_sq]
    _ = translationElement G.carrier
          (t + pointAction G.carrier c.generator u + c.shift) := by
          exact (translationElement_add G.carrier _ _).symm

/-- The order-two norm vector attached to the selected reflection action. -/
def reflectionNormVector {G : PlaneGroup} (c : ReflectionExtensionData G)
    (t : translationVectors G.carrier) : translationVectors G.carrier :=
  t + pointAction G.carrier c.generator t

/-- Multiplying the selected lift by a translation changes its square shift by a norm vector. -/
def ReflectionExtensionData.adjust {G : PlaneGroup}
    (c : ReflectionExtensionData G) (u : translationVectors G.carrier) :
    ReflectionExtensionData G where
  generator := c.generator
  generator_ne_one := c.generator_ne_one
  generator_cases := c.generator_cases
  lift := translationElement G.carrier u * c.lift
  lift_projection := by
    rw [map_mul, c.lift_projection]
    have hu : pointProjection G.carrier
        (translationElement G.carrier u) = 1 := by
      apply Subtype.ext
      rw [pointProjection_coe]
      exact linearPart_translation _
    rw [hu, one_mul]
  shift := reflectionNormVector c u + c.shift
  lift_sq := by
    simpa [reflectionDecode, reflectionNormVector, pow_two, add_assoc] using
      reflectionDecode_mul_tt c u u

/-- Coordinate transport between two reflection extensions. -/
noncomputable def reflectionNormalFormEquiv
    {G H : PlaneGroup}
    (cG : ReflectionExtensionData G) (cH : ReflectionExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier) :
    G.carrier ≃ H.carrier :=
  (reflectionDecodeEquiv cG).symm |>.trans
    ((Equiv.prodCongr eT.toEquiv (Equiv.refl Bool)).trans
      (reflectionDecodeEquiv cH))

@[simp]
theorem reflectionNormalFormEquiv_decode
    {G H : PlaneGroup}
    (cG : ReflectionExtensionData G) (cH : ReflectionExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (t : translationVectors G.carrier) (b : Bool) :
    reflectionNormalFormEquiv cG cH eT (reflectionDecode cG (t, b)) =
      reflectionDecode cH (eT t, b) := by
  change (reflectionDecodeEquiv cH)
      ((Equiv.prodCongr eT.toEquiv (Equiv.refl Bool))
        ((reflectionDecodeEquiv cG).symm
          ((reflectionDecodeEquiv cG) (t, b)))) =
    (reflectionDecodeEquiv cH) (eT t, b)
  rw [(reflectionDecodeEquiv cG).symm_apply_apply]
  rfl

/-- Exact matching of the lattice action and square shift identifies two reflection extensions. -/
noncomputable def reflectionNormalFormMulEquiv
    {G H : PlaneGroup}
    (cG : ReflectionExtensionData G) (cH : ReflectionExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hact : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction H.carrier cH.generator (eT t))
    (hshift : eT cG.shift = cH.shift) :
    G.carrier ≃* H.carrier where
  toEquiv := reflectionNormalFormEquiv cG cH eT
  map_mul' x y := by
    obtain ⟨⟨t, b⟩, rfl⟩ := reflectionDecode_surjective cG x
    obtain ⟨⟨u, d⟩, rfl⟩ := reflectionDecode_surjective cG y
    change reflectionNormalFormEquiv cG cH eT
        (reflectionDecode cG (t, b) * reflectionDecode cG (u, d)) =
      reflectionNormalFormEquiv cG cH eT (reflectionDecode cG (t, b)) *
        reflectionNormalFormEquiv cG cH eT (reflectionDecode cG (u, d))
    cases b <;> cases d
    · rw [reflectionDecode_mul_ff]
      simp only [reflectionNormalFormEquiv_decode, map_add]
      rw [reflectionDecode_mul_ff]
    · rw [reflectionDecode_mul_ft]
      simp only [reflectionNormalFormEquiv_decode, map_add]
      rw [reflectionDecode_mul_ft]
    · rw [reflectionDecode_mul_tf]
      simp only [reflectionNormalFormEquiv_decode, map_add, hact]
      rw [reflectionDecode_mul_tf]
    · rw [reflectionDecode_mul_tt]
      simp only [reflectionNormalFormEquiv_decode, map_add, hact, hshift]
      rw [reflectionDecode_mul_tt]

@[simp]
theorem reflectionNormalFormMulEquiv_translation
    {G H : PlaneGroup}
    (cG : ReflectionExtensionData G) (cH : ReflectionExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hact : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction H.carrier cH.generator (eT t))
    (hshift : eT cG.shift = cH.shift)
    (t : translationVectors G.carrier) :
    reflectionNormalFormMulEquiv cG cH eT hact hshift
        (translationElement G.carrier t) =
      translationElement H.carrier (eT t) := by
  change reflectionNormalFormEquiv cG cH eT
      (reflectionDecode cG (t, false)) = _
  exact reflectionNormalFormEquiv_decode cG cH eT t false

/-- Reusable two-coset reflection-extension isomorphism. -/
noncomputable def reflectionExtensionIso
    (G H : PlaneGroup)
    (cG : ReflectionExtensionData G) (cH : ReflectionExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hact : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction H.carrier cH.generator (eT t))
    (hshift : eT cG.shift = cH.shift) :
    TranslationPreservingIso G H := by
  let F := reflectionNormalFormMulEquiv cG cH eT hact hshift
  refine ⟨F, ?_⟩
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ :=
      (mem_translationSubgroup_iff_exists G.carrier x).mp hx
    have hxt : x = translationElement G.carrier t := by
      apply Subtype.ext
      exact ht
    rw [hxt]
    change F (translationElement G.carrier t) ∈
      translationSubgroup H.carrier
    dsimp only [F]
    rw [reflectionNormalFormMulEquiv_translation]
    change linearPart (translation (eT t : Plane)) = 1
    exact linearPart_translation _
  · intro y hy
    obtain ⟨u, hu⟩ :=
      (mem_translationSubgroup_iff_exists H.carrier y).mp hy
    let t : translationVectors G.carrier := eT.symm u
    refine ⟨translationElement G.carrier t, ?_, ?_⟩
    · change linearPart (translation (t : Plane)) = 1
      exact linearPart_translation _
    · change F (translationElement G.carrier t) = y
      dsimp only [F]
      rw [reflectionNormalFormMulEquiv_translation]
      apply Subtype.ext
      rw [eT.apply_symm_apply]
      exact hu.symm

/-- Equality of square shifts modulo the order-two norm image gives a reflection-extension
isomorphism. -/
noncomputable def reflectionExtensionIsoOfShiftDifference
    (G H : PlaneGroup)
    (cG : ReflectionExtensionData G) (cH : ReflectionExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (hact : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.generator t) =
        pointAction H.carrier cH.generator (eT t))
    (u : translationVectors H.carrier)
    (hshift : eT cG.shift = reflectionNormVector cH u + cH.shift) :
    TranslationPreservingIso G H :=
  reflectionExtensionIso G H cG (cH.adjust u) eT hact hshift

end

end WallpaperGroups
