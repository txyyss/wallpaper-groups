import WallpaperGroups.Classification.Wallpaper

set_option linter.style.header false

/-!
# Equivalence classes of plane groups

The final classification theorem identifies the quotient of all `PlaneGroup`s by
translation-preserving equivalence with the finite type of seventeen wallpaper labels.  This
file packages that quotient-level statement and its cardinality consequence.
-/

set_option autoImplicit false

namespace WallpaperGroups

noncomputable section

namespace PlaneGroup

/-- Plane groups modulo translation-preserving abstract equivalence. -/
abbrev EquivalenceClass := Quotient PlaneGroup.equivalentSetoid

end PlaneGroup

namespace WallpaperType

/-- The equivalence class represented by the standard model of a wallpaper label. -/
def toEquivalenceClass (w : WallpaperType) : PlaneGroup.EquivalenceClass :=
  Quotient.mk'' w.model

/-- Distinct wallpaper labels determine distinct plane-group equivalence classes. -/
theorem toEquivalenceClass_injective :
    Function.Injective toEquivalenceClass := by
  intro w v h
  apply (w.models_equivalent_iff v).mp
  exact Quotient.exact h

/-- Every plane-group equivalence class is represented by a standard wallpaper model. -/
theorem toEquivalenceClass_surjective :
    Function.Surjective toEquivalenceClass := by
  intro x
  induction x using Quotient.inductionOn with
  | _ G =>
      obtain ⟨w, hw, _⟩ := classification G
      refine ⟨w, Quotient.sound ?_⟩
      exact PlaneGroup.Equivalent.symm hw

/-- The standard-model map is a bijection onto plane-group equivalence classes. -/
theorem toEquivalenceClass_bijective :
    Function.Bijective toEquivalenceClass :=
  ⟨toEquivalenceClass_injective, toEquivalenceClass_surjective⟩

/-- Wallpaper labels are canonically equivalent to plane-group equivalence classes. -/
def equivalenceClassEquiv : WallpaperType ≃ PlaneGroup.EquivalenceClass :=
  Equiv.ofBijective toEquivalenceClass toEquivalenceClass_bijective

@[simp]
theorem equivalenceClassEquiv_apply (w : WallpaperType) :
    equivalenceClassEquiv w = toEquivalenceClass w :=
  rfl

/-- The finite label type has exactly seventeen elements. -/
@[simp]
theorem fintype_card_eq_seventeen : Fintype.card WallpaperType = 17 := by
  decide

/-- `Nat.card` form of the seventeen-label cardinality computation. -/
@[simp]
theorem card_eq_seventeen : Nat.card WallpaperType = 17 := by
  rw [Nat.card_eq_fintype_card]
  exact fintype_card_eq_seventeen

end WallpaperType

namespace PlaneGroup

/-- Finiteness of the quotient, transported from the finite type of wallpaper labels. -/
noncomputable instance equivalenceClassFinite : Finite PlaneGroup.EquivalenceClass :=
  Finite.of_equiv WallpaperType WallpaperType.equivalenceClassEquiv

/-- There are exactly seventeen translation-preserving equivalence classes of plane groups. -/
@[simp]
theorem equivalenceClass_card_eq_seventeen :
    Nat.card PlaneGroup.EquivalenceClass = 17 := by
  calc
    Nat.card PlaneGroup.EquivalenceClass = Nat.card WallpaperType :=
      Nat.card_congr WallpaperType.equivalenceClassEquiv.symm
    _ = 17 := WallpaperType.card_eq_seventeen

end PlaneGroup

end

end WallpaperGroups
