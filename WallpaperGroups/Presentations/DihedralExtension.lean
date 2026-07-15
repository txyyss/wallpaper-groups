import WallpaperGroups.Presentations.ReflectionExtension

set_option linter.style.header false

/-!
# Dihedral point-group extensions

This file packages a reusable normal form for the extensions used in the multiple-reflection
classification.  A normalized section chooses one affine lift of every point-group element and
sends the identity to the identity.  Every motion then has a unique form

```text
translation(t) * lift(q).
```

The multiplication table is determined by the point action and the translation-valued factor of
the section.  For a dihedral point group it is enough to prove action compatibility on a selected
rotation and reflection generator; the point-group normal form propagates it to every element.
Matching the normalized factor tables then produces a translation-preserving group isomorphism.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-- A normalized point-group section together with selected dihedral generators.  The section is
not required to be a homomorphism: its failure to preserve multiplication is the factor defined
below. -/
structure DihedralExtensionData (G : PlaneGroup) where
  /-- Selected generator of the cyclic rotation subgroup. -/
  rotationGenerator : pointGroup G.carrier
  /-- The selected rotation is nontrivial in the multiple-reflection cases. -/
  rotationGenerator_ne_one : rotationGenerator ≠ 1
  /-- Selected element in the reversing coset. -/
  reflectionGenerator : pointGroup G.carrier
  /-- The reflection generator does not belong to the cyclic rotation subgroup. -/
  reflection_not_rotation :
    reflectionGenerator ∉ Subgroup.zpowers rotationGenerator
  /-- The selected reflection is an involution in the point group. -/
  reflection_sq : reflectionGenerator ^ 2 = 1
  /-- Conjugation by the selected reflection inverts the complete rotation subgroup. -/
  reflection_conjugates : ∀ r : Subgroup.zpowers rotationGenerator,
    reflectionGenerator * r.1 * reflectionGenerator⁻¹ = (r.1)⁻¹
  /-- Every point element is a rotation or the selected reflection times a rotation. -/
  point_normal_form : ∀ q : pointGroup G.carrier,
    q ∈ Subgroup.zpowers rotationGenerator ∨
      ∃ r : Subgroup.zpowers rotationGenerator,
        q = reflectionGenerator * r.1
  /-- A selected affine lift of every point-group element. -/
  lift : pointGroup G.carrier → G.carrier
  /-- Every selected lift has the advertised point projection. -/
  lift_projection : ∀ q : pointGroup G.carrier,
    pointProjection G.carrier (lift q) = q
  /-- The section is normalized at the identity. -/
  lift_one : lift 1 = 1

/-- The defect motion measuring the failure of the selected section to preserve a product. -/
def dihedralLiftDefect {G : PlaneGroup} (c : DihedralExtensionData G)
    (q r : pointGroup G.carrier) : G.carrier :=
  c.lift q * c.lift r * (c.lift (q * r))⁻¹

/-- The lift defect has trivial point projection. -/
@[simp]
theorem dihedralLiftDefect_projection {G : PlaneGroup}
    (c : DihedralExtensionData G) (q r : pointGroup G.carrier) :
    pointProjection G.carrier (dihedralLiftDefect c q r) = 1 := by
  simp [dihedralLiftDefect, c.lift_projection]

/-- The translation-valued normalized factor of a dihedral section. -/
def dihedralFactor {G : PlaneGroup} (c : DihedralExtensionData G)
    (q r : pointGroup G.carrier) : translationVectors G.carrier := by
  let d : G.carrier := dihedralLiftDefect c q r
  refine ⟨translationPart (d : EuclideanMotion Plane), ?_⟩
  change translation (translationPart (d : EuclideanMotion Plane)) ∈ G.carrier
  have hd : linearPart (d : EuclideanMotion Plane) = 1 := by
    have hp := dihedralLiftDefect_projection c q r
    exact congrArg Subtype.val hp
  rw [← eq_translation_of_linearPart_eq_one hd]
  exact d.property

/-- The lift defect is the pure translation represented by the normalized factor. -/
theorem dihedralLiftDefect_eq_translation {G : PlaneGroup}
    (c : DihedralExtensionData G) (q r : pointGroup G.carrier) :
    (dihedralLiftDefect c q r : EuclideanMotion Plane) =
      translation (dihedralFactor c q r : Plane) := by
  apply eq_translation_of_linearPart_eq_one
  have hp := dihedralLiftDefect_projection c q r
  exact congrArg Subtype.val hp

/-- Multiplication of selected lifts produces exactly the normalized factor translation. -/
theorem dihedralLift_mul_lift {G : PlaneGroup}
    (c : DihedralExtensionData G) (q r : pointGroup G.carrier) :
    c.lift q * c.lift r =
      translationElement G.carrier (dihedralFactor c q r) * c.lift (q * r) := by
  apply Subtype.ext
  change (c.lift q : EuclideanMotion Plane) * (c.lift r : EuclideanMotion Plane) =
    translation (dihedralFactor c q r : Plane) *
      (c.lift (q * r) : EuclideanMotion Plane)
  calc
    (c.lift q : EuclideanMotion Plane) * (c.lift r : EuclideanMotion Plane) =
        ((dihedralLiftDefect c q r : G.carrier) : EuclideanMotion Plane) *
          (c.lift (q * r) : EuclideanMotion Plane) := by
            simp [dihedralLiftDefect]
    _ = translation (dihedralFactor c q r : Plane) *
          (c.lift (q * r) : EuclideanMotion Plane) := by
            rw [dihedralLiftDefect_eq_translation]

/-- The normalized factor is zero when its left argument is the identity. -/
@[simp]
theorem dihedralFactor_one_left {G : PlaneGroup}
    (c : DihedralExtensionData G) (q : pointGroup G.carrier) :
    dihedralFactor c 1 q = 0 := by
  apply Subtype.ext
  change translationPart
      ((c.lift 1 : EuclideanMotion Plane) * (c.lift q : EuclideanMotion Plane) *
        ((c.lift q : G.carrier) : EuclideanMotion Plane)⁻¹) = 0
  rw [c.lift_one]
  simp

/-- The normalized factor is zero when its right argument is the identity. -/
@[simp]
theorem dihedralFactor_one_right {G : PlaneGroup}
    (c : DihedralExtensionData G) (q : pointGroup G.carrier) :
    dihedralFactor c q 1 = 0 := by
  apply Subtype.ext
  change translationPart
      ((c.lift q : EuclideanMotion Plane) * (c.lift 1 : EuclideanMotion Plane) *
        ((c.lift q : G.carrier) : EuclideanMotion Plane)⁻¹) = 0
  rw [c.lift_one]
  simp

/-- Decode translation and point coordinates using the normalized section. -/
def dihedralDecode {G : PlaneGroup} (c : DihedralExtensionData G) :
    translationVectors G.carrier × pointGroup G.carrier → G.carrier
  | (t, q) => translationElement G.carrier t * c.lift q

/-- The point projection of a decoded normal form is its point coordinate. -/
@[simp]
theorem dihedralDecode_projection {G : PlaneGroup}
    (c : DihedralExtensionData G)
    (t : translationVectors G.carrier) (q : pointGroup G.carrier) :
    pointProjection G.carrier (dihedralDecode c (t, q)) = q := by
  simp [dihedralDecode, c.lift_projection]

/-- Every motion admits a translation-times-section normal form. -/
theorem dihedralDecode_surjective {G : PlaneGroup}
    (c : DihedralExtensionData G) : Function.Surjective (dihedralDecode c) := by
  intro x
  let q : pointGroup G.carrier := pointProjection G.carrier x
  let y : G.carrier := x * (c.lift q)⁻¹
  have hyproj : pointProjection G.carrier y = 1 := by
    simp [y, q, c.lift_projection]
  have hyker : y ∈ translationSubgroup G.carrier := by
    rw [← pointProjection_ker]
    exact hyproj
  obtain ⟨t, ht⟩ :=
    (mem_translationSubgroup_iff_exists G.carrier y).mp hyker
  have hyt : y = translationElement G.carrier t := by
    apply Subtype.ext
    exact ht
  refine ⟨(t, q), ?_⟩
  change translationElement G.carrier t * c.lift q = x
  rw [← hyt]
  simp [y]

/-- Translation-times-section coordinates are unique. -/
theorem dihedralDecode_injective {G : PlaneGroup}
    (c : DihedralExtensionData G) : Function.Injective (dihedralDecode c) := by
  rintro ⟨t, q⟩ ⟨u, r⟩ h
  have hqr : q = r := by
    have hp := congrArg (pointProjection G.carrier) h
    simpa using hp
  subst r
  have htrans : translationElement G.carrier t =
      translationElement G.carrier u := by
    exact mul_right_cancel h
  have htu : t = u := by
    apply Subtype.ext
    apply translation_injective
    exact congrArg (fun z : G.carrier => (z : EuclideanMotion Plane)) htrans
  simp [htu]

/-- Every element has unique normalized translation and point coordinates. -/
noncomputable def dihedralDecodeEquiv {G : PlaneGroup}
    (c : DihedralExtensionData G) :
    translationVectors G.carrier × pointGroup G.carrier ≃ G.carrier :=
  Equiv.ofBijective (dihedralDecode c)
    ⟨dihedralDecode_injective c, dihedralDecode_surjective c⟩

/-- Move a translation past an arbitrary selected point lift. -/
theorem dihedralLift_mul_translation {G : PlaneGroup}
    (c : DihedralExtensionData G) (q : pointGroup G.carrier)
    (t : translationVectors G.carrier) :
    c.lift q * translationElement G.carrier t =
      translationElement G.carrier (pointAction G.carrier q t) * c.lift q := by
  calc
    c.lift q * translationElement G.carrier t =
        (c.lift q * translationElement G.carrier t * (c.lift q)⁻¹) * c.lift q := by
          group
    _ = translationElement G.carrier
        (pointAction G.carrier (pointProjection G.carrier (c.lift q)) t) *
          c.lift q := by
      rw [conjugate_translationElement]
    _ = translationElement G.carrier (pointAction G.carrier q t) * c.lift q := by
      rw [c.lift_projection]

/-- Multiplication in normalized coordinates is controlled by the point action and factor. -/
theorem dihedralDecode_mul {G : PlaneGroup}
    (c : DihedralExtensionData G)
    (t u : translationVectors G.carrier)
    (q r : pointGroup G.carrier) :
    dihedralDecode c (t, q) * dihedralDecode c (u, r) =
      dihedralDecode c
        (t + pointAction G.carrier q u + dihedralFactor c q r, q * r) := by
  change (translationElement G.carrier t * c.lift q) *
      (translationElement G.carrier u * c.lift r) =
    translationElement G.carrier
        (t + pointAction G.carrier q u + dihedralFactor c q r) *
      c.lift (q * r)
  calc
    (translationElement G.carrier t * c.lift q) *
        (translationElement G.carrier u * c.lift r) =
      (translationElement G.carrier t *
        (c.lift q * translationElement G.carrier u)) * c.lift r := by
          group
    _ = (translationElement G.carrier t *
        (translationElement G.carrier (pointAction G.carrier q u) * c.lift q)) *
          c.lift r := by
            rw [dihedralLift_mul_translation]
    _ = (translationElement G.carrier t *
        translationElement G.carrier (pointAction G.carrier q u)) *
          (c.lift q * c.lift r) := by
            group
    _ = translationElement G.carrier
          (t + pointAction G.carrier q u) *
        (translationElement G.carrier (dihedralFactor c q r) *
          c.lift (q * r)) := by
            rw [← translationElement_add, dihedralLift_mul_lift]
    _ = translationElement G.carrier
          (t + pointAction G.carrier q u + dihedralFactor c q r) *
        c.lift (q * r) := by
          rw [← mul_assoc, ← translationElement_add]

/-- Coordinate transport between two normalized dihedral extensions. -/
noncomputable def dihedralNormalFormEquiv
    {G H : PlaneGroup}
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier) :
    G.carrier ≃ H.carrier :=
  (dihedralDecodeEquiv cG).symm |>.trans
    ((Equiv.prodCongr eT.toEquiv eP.toEquiv).trans
      (dihedralDecodeEquiv cH))

/-- Coordinate transport acts componentwise on decoded normal forms. -/
@[simp]
theorem dihedralNormalFormEquiv_decode
    {G H : PlaneGroup}
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (t : translationVectors G.carrier) (q : pointGroup G.carrier) :
    dihedralNormalFormEquiv cG cH eT eP (dihedralDecode cG (t, q)) =
      dihedralDecode cH (eT t, eP q) := by
  change (dihedralDecodeEquiv cH)
      ((Equiv.prodCongr eT.toEquiv eP.toEquiv)
        ((dihedralDecodeEquiv cG).symm ((dihedralDecodeEquiv cG) (t, q)))) =
    (dihedralDecodeEquiv cH) (eT t, eP q)
  rw [(dihedralDecodeEquiv cG).symm_apply_apply]
  rfl

/-- Exact compatibility of point actions and normalized factors identifies two extensions. -/
noncomputable def dihedralNormalFormMulEquiv
    {G H : PlaneGroup}
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (hact : ∀ (q : pointGroup G.carrier) (t : translationVectors G.carrier),
      eT (pointAction G.carrier q t) =
        pointAction H.carrier (eP q) (eT t))
    (hfactor : ∀ q r : pointGroup G.carrier,
      eT (dihedralFactor cG q r) = dihedralFactor cH (eP q) (eP r)) :
    G.carrier ≃* H.carrier where
  toEquiv := dihedralNormalFormEquiv cG cH eT eP
  map_mul' x y := by
    obtain ⟨⟨t, q⟩, rfl⟩ := dihedralDecode_surjective cG x
    obtain ⟨⟨u, r⟩, rfl⟩ := dihedralDecode_surjective cG y
    change dihedralNormalFormEquiv cG cH eT eP
        (dihedralDecode cG (t, q) * dihedralDecode cG (u, r)) =
      dihedralNormalFormEquiv cG cH eT eP (dihedralDecode cG (t, q)) *
        dihedralNormalFormEquiv cG cH eT eP (dihedralDecode cG (u, r))
    rw [dihedralDecode_mul]
    simp only [dihedralNormalFormEquiv_decode, map_add, map_mul,
      hact, hfactor]
    rw [dihedralDecode_mul]

/-- The normal-form isomorphism sends every pure translation through the supplied additive
equivalence. -/
@[simp]
theorem dihedralNormalFormMulEquiv_translation
    {G H : PlaneGroup}
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (hact : ∀ (q : pointGroup G.carrier) (t : translationVectors G.carrier),
      eT (pointAction G.carrier q t) =
        pointAction H.carrier (eP q) (eT t))
    (hfactor : ∀ q r : pointGroup G.carrier,
      eT (dihedralFactor cG q r) = dihedralFactor cH (eP q) (eP r))
    (t : translationVectors G.carrier) :
    dihedralNormalFormMulEquiv cG cH eT eP hact hfactor
        (translationElement G.carrier t) =
      translationElement H.carrier (eT t) := by
  have hsource : dihedralDecode cG (t, 1) = translationElement G.carrier t := by
    simp [dihedralDecode, cG.lift_one]
  rw [← hsource]
  change dihedralNormalFormEquiv cG cH eT eP (dihedralDecode cG (t, 1)) = _
  rw [dihedralNormalFormEquiv_decode]
  simp [dihedralDecode, cH.lift_one]

/-- The normal-form isomorphism transports point projections through the supplied point-group
equivalence. -/
@[simp]
theorem dihedralNormalFormMulEquiv_pointProjection
    {G H : PlaneGroup}
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (hact : ∀ (q : pointGroup G.carrier) (t : translationVectors G.carrier),
      eT (pointAction G.carrier q t) =
        pointAction H.carrier (eP q) (eT t))
    (hfactor : ∀ q r : pointGroup G.carrier,
      eT (dihedralFactor cG q r) = dihedralFactor cH (eP q) (eP r))
    (x : G.carrier) :
    pointProjection H.carrier
        (dihedralNormalFormMulEquiv cG cH eT eP hact hfactor x) =
      eP (pointProjection G.carrier x) := by
  obtain ⟨⟨t, q⟩, rfl⟩ := dihedralDecode_surjective cG x
  change pointProjection H.carrier
      (dihedralNormalFormEquiv cG cH eT eP (dihedralDecode cG (t, q))) = _
  rw [dihedralNormalFormEquiv_decode]
  simp

/-- Matching normalized section data gives a translation-preserving isomorphism. -/
noncomputable def dihedralExtensionIso
    (G H : PlaneGroup)
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (hact : ∀ (q : pointGroup G.carrier) (t : translationVectors G.carrier),
      eT (pointAction G.carrier q t) =
        pointAction H.carrier (eP q) (eT t))
    (hfactor : ∀ q r : pointGroup G.carrier,
      eT (dihedralFactor cG q r) = dihedralFactor cH (eP q) (eP r)) :
    TranslationPreservingIso G H := by
  let F := dihedralNormalFormMulEquiv cG cH eT eP hact hfactor
  refine ⟨F, ?_⟩
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ :=
      (mem_translationSubgroup_iff_exists G.carrier x).mp hx
    have hxt : x = translationElement G.carrier t := by
      apply Subtype.ext
      exact ht
    rw [hxt]
    change F (translationElement G.carrier t) ∈ translationSubgroup H.carrier
    dsimp only [F]
    rw [dihedralNormalFormMulEquiv_translation]
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
      rw [dihedralNormalFormMulEquiv_translation]
      apply Subtype.ext
      rw [eT.apply_symm_apply]
      exact hu.symm

/-- Intertwining the selected rotation and reflection actions intertwines every point action. -/
theorem dihedral_action_equivariant_of_generators
    (G H : PlaneGroup)
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (hrotation : eP cG.rotationGenerator = cH.rotationGenerator)
    (hreflection : eP cG.reflectionGenerator = cH.reflectionGenerator)
    (hrotationAction : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.rotationGenerator t) =
        pointAction H.carrier cH.rotationGenerator (eT t))
    (hreflectionAction : ∀ t : translationVectors G.carrier,
      eT (pointAction G.carrier cG.reflectionGenerator t) =
        pointAction H.carrier cH.reflectionGenerator (eT t)) :
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
  have hrot : cG.rotationGenerator ∈ K := by
    intro t
    rw [hrotation]
    exact hrotationAction t
  have hrefl : cG.reflectionGenerator ∈ K := by
    intro t
    rw [hreflection]
    exact hreflectionAction t
  have hz : Subgroup.zpowers cG.rotationGenerator ≤ K :=
    Subgroup.zpowers_le.mpr hrot
  intro q t
  rcases cG.point_normal_form q with hq | ⟨r, rfl⟩
  · exact hz hq t
  · exact K.mul_mem hrefl (hz r.property) t

/-- Compatibility data expressing equality of two normalized dihedral extensions. -/
structure DihedralNormalizedDataEquiv
    {G H : PlaneGroup}
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier) : Prop where
  /-- The point equivalence matches the selected rotation generators. -/
  map_rotation : eP cG.rotationGenerator = cH.rotationGenerator
  /-- The point equivalence matches the selected reflection generators. -/
  map_reflection : eP cG.reflectionGenerator = cH.reflectionGenerator
  /-- The translation equivalence intertwines the selected rotation actions. -/
  rotation_action : ∀ t : translationVectors G.carrier,
    eT (pointAction G.carrier cG.rotationGenerator t) =
      pointAction H.carrier cH.rotationGenerator (eT t)
  /-- The translation equivalence intertwines the selected reflection actions. -/
  reflection_action : ∀ t : translationVectors G.carrier,
    eT (pointAction G.carrier cG.reflectionGenerator t) =
      pointAction H.carrier cH.reflectionGenerator (eT t)
  /-- The complete normalized factor tables agree. -/
  factor : ∀ q r : pointGroup G.carrier,
    eT (dihedralFactor cG q r) = dihedralFactor cH (eP q) (eP r)

/-- Same normalized dihedral data determine a translation-preserving isomorphism. -/
noncomputable def dihedralExtensionIsoOfNormalizedData
    (G H : PlaneGroup)
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eT : translationVectors G.carrier ≃+ translationVectors H.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (h : DihedralNormalizedDataEquiv cG cH eT eP) :
    TranslationPreservingIso G H :=
  dihedralExtensionIso G H cG cH eT eP
    (dihedral_action_equivariant_of_generators G H cG cH eT eP
      h.map_rotation h.map_reflection h.rotation_action h.reflection_action)
    h.factor

/-- Lattice-level wrapper for the normalized dihedral-extension isomorphism. -/
noncomputable def dihedralExtensionIsoOfLatticeEquiv
    (G H : PlaneGroup)
    (cG : DihedralExtensionData G) (cH : DihedralExtensionData H)
    (eL : G.translationLattice.carrier ≃ₗ[ℤ] H.translationLattice.carrier)
    (eP : pointGroup G.carrier ≃* pointGroup H.carrier)
    (hrotation : eP cG.rotationGenerator = cH.rotationGenerator)
    (hreflection : eP cG.reflectionGenerator = cH.reflectionGenerator)
    (hrotationAction : ∀ t : G.translationLattice.carrier,
      eL (G.latticeAction cG.rotationGenerator t) =
        H.latticeAction cH.rotationGenerator (eL t))
    (hreflectionAction : ∀ t : G.translationLattice.carrier,
      eL (G.latticeAction cG.reflectionGenerator t) =
        H.latticeAction cH.reflectionGenerator (eL t))
    (hfactor : ∀ q r : pointGroup G.carrier,
      translationVectorEquivOfLatticeEquiv G H eL (dihedralFactor cG q r) =
        dihedralFactor cH (eP q) (eP r)) :
    TranslationPreservingIso G H := by
  let eT := translationVectorEquivOfLatticeEquiv G H eL
  apply dihedralExtensionIsoOfNormalizedData G H cG cH eT eP
  refine
    { map_rotation := hrotation
      map_reflection := hreflection
      rotation_action := ?_
      reflection_action := ?_
      factor := hfactor }
  · exact translationVectorEquivOfLatticeEquiv_intertwine G H eL
      cG.rotationGenerator cH.rotationGenerator hrotationAction
  · exact translationVectorEquivOfLatticeEquiv_intertwine G H eL
      cG.reflectionGenerator cH.reflectionGenerator hreflectionAction

end

end WallpaperGroups
