import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.Tactic.Abel
import WallpaperGroups.Extensions.TwistedProduct

set_option linter.style.header false

/-!
# Normalized sections and extension factors

This file extracts a normalized cocycle from a mathlib `GroupExtension` equipped with a normalized
set-theoretic section and a prescribed additive quotient action.  The kernel coordinate is
formally noncomputable for an arbitrary extension, but `inl_factor` and `factor_eq_iff` characterize
it uniquely through the injective kernel map.

If a section is changed by a kernel-valued normalized cochain, the extracted factor changes by the
explicit coboundary convention fixed in `NormalizedCocycle.lean`.
-/

set_option autoImplicit false

namespace WallpaperGroups

variable {N E H T : Type*}
variable [Group N] [Group E] [Group H] [AddCommGroup T]

/-- A set-theoretic section of a group extension which sends the identity to the identity. -/
structure NormalizedSection (S : GroupExtension N E H) extends S.Section where
  /-- The section is normalized at the quotient identity. -/
  map_one : toSection 1 = 1

namespace NormalizedSection

variable {S : GroupExtension N E H}

instance : FunLike (NormalizedSection S) H E where
  coe s := s.toSection
  coe_injective s t h := by
    cases s
    cases t
    simp_all

@[simp]
theorem rightHom_apply (s : NormalizedSection S) (h : H) :
    S.rightHom (s h) = h :=
  s.toSection.rightHom_section h

@[simp]
theorem apply_one (s : NormalizedSection S) :
    s 1 = 1 :=
  s.map_one

/-- Normalize a supplied section by left-multiplying by the inverse of its value at `1`. -/
def normalize (σ : S.Section) : NormalizedSection S where
  toSection :=
    { toFun := fun h ↦ (σ 1)⁻¹ * σ h
      rightInverse_rightHom := by
        intro h
        simp }
  map_one := inv_mul_cancel (σ 1)

end NormalizedSection

namespace NormalizedSection

variable {S : GroupExtension (Multiplicative T) E H}
variable {ρ : AdditiveAction H T}

/-- The additive kernel coordinate of the defect
`s(g) * s(h) * s(gh)⁻¹` of a normalized section. -/
noncomputable def factor (s : NormalizedSection S) (g h : H) : T :=
  (Function.invFun S.inl (s g * s h * (s (g * h))⁻¹)).toAdd

/-- The factor is uniquely characterized by its image under the kernel inclusion. -/
theorem inl_factor (s : NormalizedSection S) (g h : H) :
    S.inl (Multiplicative.ofAdd (factor s g h)) =
      s g * s h * (s (g * h))⁻¹ := by
  unfold factor
  apply Function.invFun_eq
  exact s.toSection.mul_mul_mul_inv_mem_range_inl g h

/-- A candidate is the section factor exactly when its kernel image is the section defect. -/
theorem factor_eq_iff (s : NormalizedSection S) (g h : H) (t : T) :
    factor s g h = t ↔
      S.inl (Multiplicative.ofAdd t) =
        s g * s h * (s (g * h))⁻¹ := by
  constructor
  · intro hfactor
    rw [← hfactor]
    exact inl_factor s g h
  · intro ht
    apply Multiplicative.ofAdd.injective
    apply S.inl_injective
    rw [inl_factor]
    exact ht.symm

/-- Multiplication of section values is controlled by the extracted factor. -/
theorem mul_eq_inl_factor_mul (s : NormalizedSection S) (g h : H) :
    s g * s h =
      S.inl (Multiplicative.ofAdd (factor s g h)) * s (g * h) := by
  rw [inl_factor]
  group

@[simp]
theorem factor_one_left (s : NormalizedSection S) (h : H) :
    factor s 1 h = 0 := by
  apply Multiplicative.ofAdd.injective
  apply S.inl_injective
  rw [inl_factor]
  simp

@[simp]
theorem factor_one_right (s : NormalizedSection S) (g : H) :
    factor s g 1 = 0 := by
  apply Multiplicative.ofAdd.injective
  apply S.inl_injective
  rw [inl_factor]
  simp

/-- A section of an extension over `ρ` realizes the prescribed action on the kernel. -/
theorem conjugation_inl
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (h : H) (t : T) :
    X.inl (Multiplicative.ofAdd (ρ.apply h t)) =
      s h * X.inl (Multiplicative.ofAdd t) * (s h)⁻¹ := by
  simpa using X.conjugation_inl (s h) t

/-- The extracted factor satisfies the cocycle identity.  This is the group-associativity
calculation for the section normal form. -/
theorem factor_cocycle
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (g h k : H) :
    factor s g h + factor s (g * h) k =
      ρ.apply g (factor s h k) + factor s g (h * k) := by
  apply Multiplicative.ofAdd.injective
  apply X.toGroupExtension.inl_injective
  rw [ofAdd_add, ofAdd_add, map_mul, map_mul]
  change
    X.inl (Multiplicative.ofAdd (factor s g h)) *
        X.inl (Multiplicative.ofAdd (factor s (g * h) k)) =
      X.inl (Multiplicative.ofAdd (ρ.apply g (factor s h k))) *
        X.inl (Multiplicative.ofAdd (factor s g (h * k)))
  rw [conjugation_inl X s, inl_factor, inl_factor, inl_factor,
    inl_factor]
  group

/-- Extract the normalized cocycle associated to a normalized section. -/
noncomputable def toCocycle
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension) :
    NormalizedCocycle ρ where
  toFun := factor s
  one_left := factor_one_left s
  one_right := factor_one_right s
  cocycle := factor_cocycle X s

@[simp]
theorem toCocycle_apply
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (g h : H) :
    s.toCocycle X g h = factor s g h :=
  rfl

/-- The additive kernel coordinate comparing two normalized sections pointwise. -/
noncomputable def difference
    (s' s : NormalizedSection S) (g : H) : T :=
  (Function.invFun S.inl (s' g * (s g)⁻¹)).toAdd

/-- The section difference is uniquely characterized by its kernel image. -/
theorem inl_difference (s' s : NormalizedSection S) (g : H) :
    S.inl (Multiplicative.ofAdd (difference s' s g)) =
      s' g * (s g)⁻¹ := by
  unfold difference
  apply Function.invFun_eq
  exact s'.toSection.mul_inv_mem_range_inl s.toSection g

@[simp]
theorem difference_one (s' s : NormalizedSection S) :
    difference s' s 1 = 0 := by
  apply Multiplicative.ofAdd.injective
  apply S.inl_injective
  rw [inl_difference]
  simp

/-- The difference between two normalized sections, bundled as a normalized cochain. -/
noncomputable def differenceCochain
    (s' s : NormalizedSection S) : NormalizedCochain H T where
  toFun := difference s' s
  map_one := difference_one s' s

@[simp]
theorem differenceCochain_apply
    (s' s : NormalizedSection S) (g : H) :
    differenceCochain s' s g = difference s' s g :=
  rfl

/-- Reconstruct one section from another and their pointwise kernel difference. -/
theorem apply_eq_inl_difference_mul
    (s' s : NormalizedSection S) (g : H) :
    s' g =
      S.inl (Multiplicative.ofAdd (difference s' s g)) * s g := by
  rw [inl_difference]
  group

/-- Changing a normalized section changes its factor by the explicit coboundary formula. -/
theorem factor_change
    (X : ExtensionOverAction (E := E) ρ)
    (s' s : NormalizedSection X.toGroupExtension)
    (g h : H) :
    factor s' g h =
      difference s' s g + ρ.apply g (difference s' s h) +
        factor s g h - difference s' s (g * h) := by
  apply Multiplicative.ofAdd.injective
  apply X.toGroupExtension.inl_injective
  rw [ofAdd_sub, map_div, ofAdd_add, map_mul, ofAdd_add, map_mul]
  rw [inl_factor]
  rw [inl_difference s' s g, inl_difference s' s (g * h)]
  rw [conjugation_inl X s]
  rw [inl_difference s' s h, inl_factor]
  simp only [div_eq_mul_inv]
  group

/-- Section change is exactly change of the extracted cocycle by the difference coboundary. -/
theorem toCocycle_change
    (X : ExtensionOverAction (E := E) ρ)
    (s' s : NormalizedSection X.toGroupExtension) :
    s'.toCocycle X =
      (s.toCocycle X).changeBy (differenceCochain s' s) := by
  ext g h
  change factor s' g h =
    factor s g h +
      (difference s' s g + ρ.apply g (difference s' s h) -
        difference s' s (g * h))
  rw [factor_change X]
  abel

end NormalizedSection

namespace TwistedProduct

variable {ρ : AdditiveAction H T}

/-- The canonical normalized section of a twisted-product extension. -/
def canonicalSection (c : NormalizedCocycle ρ) :
    NormalizedSection (toExtensionOverAction c).toGroupExtension where
  toSection :=
    { toFun := fun h ↦ ⟨0, h⟩
      rightInverse_rightHom := fun _ ↦ rfl }
  map_one := rfl

@[simp]
theorem canonicalSection_left (c : NormalizedCocycle ρ) (h : H) :
    (canonicalSection c h).left = 0 :=
  rfl

@[simp]
theorem canonicalSection_right (c : NormalizedCocycle ρ) (h : H) :
    (canonicalSection c h).right = h :=
  rfl

/-- The canonical section multiplication has exactly the input cocycle as factor. -/
theorem canonicalSection_mul
    (c : NormalizedCocycle ρ) (g h : H) :
    canonicalSection c g * canonicalSection c h =
      inl c (Multiplicative.ofAdd (c g h)) *
        canonicalSection c (g * h) := by
  ext <;> simp

/-- Extracting the factor from the canonical twisted-product section recovers the input cocycle. -/
theorem canonicalSection_toCocycle
    (c : NormalizedCocycle ρ) :
    (canonicalSection c).toCocycle (toExtensionOverAction c) = c := by
  ext g h
  change NormalizedSection.factor (canonicalSection c) g h = c g h
  apply Multiplicative.ofAdd.injective
  apply (toExtensionOverAction c).toGroupExtension.inl_injective
  change
    (toExtensionOverAction c).toGroupExtension.inl
        (Multiplicative.ofAdd (NormalizedSection.factor (canonicalSection c) g h)) =
      (toExtensionOverAction c).toGroupExtension.inl
        (Multiplicative.ofAdd (c g h))
  rw [NormalizedSection.inl_factor, canonicalSection_mul]
  simp

end TwistedProduct

end WallpaperGroups
