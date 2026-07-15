import WallpaperGroups.Presentations.TwoReflectionExtension

set_option linter.style.header false

/-!
# Intrinsic counts of vanishing reflection shifts

Every orientation-reversing point element is an involution, so any of its lifts has a canonical
order-two quotient-valued shift class.  This file records whether that class vanishes, proves
that the answer is independent of the chosen lift, and counts the reversing points for which it
vanishes.  The resulting count is intrinsic under translation-preserving isomorphism.
-/

set_option autoImplicit false

namespace WallpaperGroups

open EuclideanMotion

noncomputable section

/-- An orientation-reversing element of the finite point group. -/
abbrev ReversingPoint (G : PlaneGroup) :=
  {s : pointGroup G.carrier // s ∉ orientationPreservingPointGroup G}

instance reversingPointFinite (G : PlaneGroup) : Finite (ReversingPoint G) :=
  Finite.of_injective Subtype.val Subtype.val_injective

namespace ReversingPoint

variable {G : PlaneGroup}

/-- Every reversing point is an involution. -/
theorem sq (s : ReversingPoint G) : s.1 ^ 2 = 1 :=
  pointGroup_reversing_sq G s.1 s.2

/-- A fixed, arbitrary lift used only to define the intrinsic vanishing predicate. -/
def lift (s : ReversingPoint G) : G.carrier :=
  Classical.choose (pointProjection_surjective G.carrier s.1)

/-- The chosen motion projects to the specified reversing point. -/
@[simp]
theorem lift_projection (s : ReversingPoint G) :
    pointProjection G.carrier s.lift = s.1 :=
  Classical.choose_spec (pointProjection_surjective G.carrier s.1)

end ReversingPoint

/-- The order-two quotient shift of a reversing point vanishes.  Although the definition uses a
chosen lift, `reflectionShiftVanishes_iff_lift` below shows that the proposition is independent
of this choice. -/
def reflectionShiftVanishes (G : PlaneGroup) (s : ReversingPoint G) : Prop :=
  shiftClass G s.1 2 s.sq s.lift s.lift_projection = 0

/-- The shift class computed from the chosen lift agrees with the class computed from any other
lift of the same reversing point. -/
theorem reflectionShiftClass_lift_independent
    (G : PlaneGroup) (s : ReversingPoint G)
    (g : G.carrier) (hg : pointProjection G.carrier g = s.1) :
    shiftClass G s.1 2 s.sq s.lift s.lift_projection =
      shiftClass G s.1 2 s.sq g hg :=
  shiftClass_lift_independent G s.1 2 s.sq s.lift g s.lift_projection hg

/-- Lift-independent characterization of vanishing for an arbitrary lift. -/
theorem reflectionShiftVanishes_iff_lift
    (G : PlaneGroup) (s : ReversingPoint G)
    (g : G.carrier) (hg : pointProjection G.carrier g = s.1) :
    reflectionShiftVanishes G s ↔ shiftClass G s.1 2 s.sq g hg = 0 := by
  unfold reflectionShiftVanishes
  rw [reflectionShiftClass_lift_independent G s g hg]

namespace TranslationPreservingIso

variable {G H : PlaneGroup}

/-- A translation-preserving isomorphism bijects the reversing elements of the two point
groups. -/
def reversingPointEquiv (e : TranslationPreservingIso G H) :
    ReversingPoint G ≃ ReversingPoint H :=
  e.pointGroupEquiv.toEquiv.subtypeEquiv fun s =>
    (not_congr (e.pointGroupEquiv_mem_orientationPreserving_iff s)).symm

/-- The reversing-point equivalence is the induced point-group equivalence on values. -/
@[simp]
theorem reversingPointEquiv_coe (e : TranslationPreservingIso G H)
    (s : ReversingPoint G) :
    (e.reversingPointEquiv s).1 = e.pointGroupEquiv s.1 :=
  rfl

/-- Vanishing of the intrinsic order-two reflection shift is preserved and reflected by a
translation-preserving isomorphism. -/
theorem reflectionShiftVanishes_iff (e : TranslationPreservingIso G H)
    (s : ReversingPoint G) :
    reflectionShiftVanishes G s ↔
      reflectionShiftVanishes H (e.reversingPointEquiv s) := by
  have hmap : pointProjection H.carrier (e.toMulEquiv s.lift) =
      (e.reversingPointEquiv s).1 := by
    simpa using mappedLiftProjection e s.1 s.lift s.lift_projection
  rw [reflectionShiftVanishes_iff_lift G s s.lift s.lift_projection,
    reflectionShiftVanishes_iff_lift H (e.reversingPointEquiv s)
      (e.toMulEquiv s.lift) hmap]
  simp only [reversingPointEquiv_coe]
  have hind := shiftClass_lift_independent H (e.pointGroupEquiv s.1) 2
    (transportedPointPowerProof e s.1 2 s.sq)
    (e.toMulEquiv s.lift) (e.toMulEquiv s.lift)
    (mappedLiftProjection e s.1 s.lift s.lift_projection) hmap
  rw [← hind]
  exact shiftClass_eq_zero_iff_map e s.1 2 s.sq s.lift s.lift_projection

end TranslationPreservingIso

/-- Reversing point elements whose intrinsic order-two reflection shift vanishes. -/
abbrev VanishingReversingPoint (G : PlaneGroup) :=
  {s : ReversingPoint G // reflectionShiftVanishes G s}

instance vanishingReversingPointFinite (G : PlaneGroup) :
    Finite (VanishingReversingPoint G) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The number of reversing point elements with vanishing reflection shift. -/
def vanishingReversingPointCount (G : PlaneGroup) : ℕ :=
  Nat.card (VanishingReversingPoint G)

namespace DihedralGenerators

variable {G : PlaneGroup}

open TwoReflectionExtensionData

/-- Every `sr` coordinate in the canonical dihedral presentation is orientation reversing. -/
theorem pointDihedralHom_sr_reversing (d : DihedralGenerators G)
    (i : ZMod d.order.toNat) :
    pointDihedralHom d (.sr i) ∉ orientationPreservingPointGroup G := by
  intro hsr
  have hrinv := (orientationPreservingPointGroup G).inv_mem
    (pointRotationHom_mem_orientationPreserving d (Multiplicative.ofAdd i))
  have hfirst := (orientationPreservingPointGroup G).mul_mem hsr hrinv
  apply d.reflection_reversing
  simpa [pointDihedralHom_sr, mul_assoc] using hfirst

/-- The reversing point represented by a finite dihedral reflection coordinate. -/
def indexedReversingPoint (d : DihedralGenerators G) (i : ZMod d.order.toNat) :
    ReversingPoint G :=
  ⟨pointDihedralHom d (.sr i), d.pointDihedralHom_sr_reversing i⟩

/-- Distinct reflection coordinates give distinct reversing point elements. -/
theorem indexedReversingPoint_injective (d : DihedralGenerators G) :
    Function.Injective d.indexedReversingPoint := by
  intro i j hij
  have hword := pointDihedralHom_injective d (congrArg Subtype.val hij)
  exact DihedralGroup.sr.inj hword

/-- Every reversing point has an `sr` coordinate.  A rotation coordinate is excluded by its
orientation-preserving action. -/
theorem indexedReversingPoint_surjective (d : DihedralGenerators G) :
    Function.Surjective d.indexedReversingPoint := by
  intro s
  obtain ⟨q, hq⟩ := pointDihedralHom_surjective d s.1
  cases q with
  | r i =>
      exfalso
      apply s.2
      rw [← hq]
      exact pointRotationHom_mem_orientationPreserving d (Multiplicative.ofAdd i)
  | sr i =>
      exact ⟨i, Subtype.ext hq⟩

/-- Canonical finite coordinates for all orientation-reversing point elements. -/
def reversingPointEquiv (d : DihedralGenerators G) :
    ZMod d.order.toNat ≃ ReversingPoint G :=
  Equiv.ofBijective d.indexedReversingPoint
    ⟨d.indexedReversingPoint_injective, d.indexedReversingPoint_surjective⟩

@[simp]
theorem reversingPointEquiv_apply (d : DihedralGenerators G)
    (i : ZMod d.order.toNat) :
    d.reversingPointEquiv i = d.indexedReversingPoint i :=
  rfl

/-- On values, the reversing-point coordinate equivalence is the canonical `sr` point word. -/
@[simp]
theorem reversingPointEquiv_coe (d : DihedralGenerators G)
    (i : ZMod d.order.toNat) :
    (d.reversingPointEquiv i).1 = pointDihedralHom d (.sr i) :=
  rfl

/-- Reflection coordinates whose intrinsic order-two shift vanishes. -/
abbrev VanishingReversingPointIndex (d : DihedralGenerators G) :=
  {i : ZMod d.order.toNat // reflectionShiftVanishes G (d.indexedReversingPoint i)}

instance vanishingReversingPointIndexFinite (d : DihedralGenerators G) :
    Finite d.VanishingReversingPointIndex :=
  Finite.of_injective
    (fun i => d.indexedReversingPoint i.1)
    (fun _ _ hij => Subtype.ext (d.indexedReversingPoint_injective hij))

/-- Restricting the `ZMod` coordinate equivalence identifies the finite vanishing predicates. -/
def vanishingReversingPointIndexEquiv (d : DihedralGenerators G) :
    d.VanishingReversingPointIndex ≃ VanishingReversingPoint G :=
  d.reversingPointEquiv.subtypeEquiv fun _ => Iff.rfl

/-- The intrinsic count can be computed as a finite subtype of `ZMod d.order.toNat`. -/
theorem vanishingReversingPointCount_eq_index_natCard (d : DihedralGenerators G) :
    vanishingReversingPointCount G = Nat.card d.VanishingReversingPointIndex := by
  unfold vanishingReversingPointCount
  exact (Nat.card_congr d.vanishingReversingPointIndexEquiv).symm

end DihedralGenerators

namespace TranslationPreservingIso

variable {G H : PlaneGroup}

/-- The reversing-point equivalence restricts to the vanishing-shift subtypes. -/
def vanishingReversingPointEquiv (e : TranslationPreservingIso G H) :
    VanishingReversingPoint G ≃ VanishingReversingPoint H :=
  e.reversingPointEquiv.subtypeEquiv fun s => e.reflectionShiftVanishes_iff s

/-- Equivalent plane groups have the same number of vanishing reversing points. -/
theorem vanishingReversingPoint_natCard (e : TranslationPreservingIso G H) :
    Nat.card (VanishingReversingPoint G) =
      Nat.card (VanishingReversingPoint H) :=
  Nat.card_congr e.vanishingReversingPointEquiv

/-- Count-valued form of `vanishingReversingPoint_natCard`. -/
theorem vanishingReversingPointCount_eq (e : TranslationPreservingIso G H) :
    vanishingReversingPointCount G = vanishingReversingPointCount H :=
  e.vanishingReversingPoint_natCard

end TranslationPreservingIso

end

end WallpaperGroups
