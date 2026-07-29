import Mathlib.GroupTheory.GroupExtension.Defs

set_option linter.style.header false

/-!
# Explicit additive actions and group extensions

This file fixes the dimension-independent action convention used by the explicit cocycle API.
An action is ordinary data

```text
ρ : H →* Multiplicative (AddAut T),
```

so different actions can be compared without installing competing typeclass instances.  The
`ExtensionOverAction` wrapper keeps mathlib's `GroupExtension` as the short-exact-sequence
foundation and records only the compatibility of conjugation with the prescribed action.
-/

set_option autoImplicit false

namespace WallpaperGroups

/-- An explicit left action of a group `H` on an additive commutative group `T`. -/
abbrev AdditiveAction (H T : Type*) [Group H] [AddCommGroup T] :=
  H →* Multiplicative (AddAut T)

namespace AdditiveAction

variable {H T : Type*} [Group H] [AddCommGroup T]

/-- Evaluate an explicit additive action. -/
def apply (ρ : AdditiveAction H T) (h : H) (t : T) : T :=
  (ρ h).toAdd t

@[simp]
theorem apply_one (ρ : AdditiveAction H T) (t : T) :
    ρ.apply 1 t = t := by
  change (ρ 1).toAdd t = t
  rw [map_one]
  rfl

theorem apply_mul (ρ : AdditiveAction H T) (g h : H) (t : T) :
    ρ.apply (g * h) t = ρ.apply g (ρ.apply h t) := by
  change (ρ (g * h)).toAdd t = (ρ g).toAdd ((ρ h).toAdd t)
  rw [map_mul]
  rfl

@[simp]
theorem apply_zero (ρ : AdditiveAction H T) (h : H) :
    ρ.apply h 0 = 0 :=
  (ρ h).toAdd.map_zero

@[simp]
theorem apply_add (ρ : AdditiveAction H T) (h : H) (t u : T) :
    ρ.apply h (t + u) = ρ.apply h t + ρ.apply h u :=
  (ρ h).toAdd.map_add t u

@[simp]
theorem apply_neg (ρ : AdditiveAction H T) (h : H) (t : T) :
    ρ.apply h (-t) = -ρ.apply h t :=
  (ρ h).toAdd.map_neg t

@[simp]
theorem apply_sub (ρ : AdditiveAction H T) (h : H) (t u : T) :
    ρ.apply h (t - u) = ρ.apply h t - ρ.apply h u :=
  (ρ h).toAdd.map_sub t u

end AdditiveAction

namespace GroupExtension

variable {N N' E H : Type*} [Group N] [Group N'] [Group E] [Group H]

/-- Reparameterize the kernel endpoint of an existing group extension along a group equivalence.

This changes only the presentation of the left endpoint; the middle group, quotient, and short
exact sequence are reused unchanged.
-/
def relabelKernel (S : GroupExtension N E H) (e : N' ≃* N) :
    GroupExtension N' E H where
  inl := S.inl.comp e.toMonoidHom
  rightHom := S.rightHom
  inl_injective := S.inl_injective.comp e.injective
  range_inl_eq_ker_rightHom := by
    rw [← S.range_inl_eq_ker_rightHom]
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨e.symm n, by simp⟩
  rightHom_surjective := S.rightHom_surjective

@[simp]
theorem relabelKernel_inl (S : GroupExtension N E H) (e : N' ≃* N) (n : N') :
    (relabelKernel S e).inl n = S.inl (e n) :=
  rfl

@[simp]
theorem relabelKernel_rightHom (S : GroupExtension N E H) (e : N' ≃* N) (x : E) :
    (relabelKernel S e).rightHom x = S.rightHom x :=
  rfl

end GroupExtension

variable {H T E : Type*} [Group H] [AddCommGroup T] [Group E]

/-- A group extension of `H` by the additive group `T` whose conjugation action is the specified
explicit action `ρ`.

The kernel is represented multiplicatively as `Multiplicative T`; the underlying short exact
sequence remains mathlib's `GroupExtension`.
-/
structure ExtensionOverAction (ρ : AdditiveAction H T) where
  /-- The underlying short exact sequence. -/
  toGroupExtension : GroupExtension (Multiplicative T) E H
  /-- Conjugation by a middle-group element agrees with the prescribed quotient action. -/
  conjugation_inl :
    ∀ (e : E) (t : T),
      toGroupExtension.inl (Multiplicative.ofAdd (ρ.apply (toGroupExtension.rightHom e) t)) =
        e * toGroupExtension.inl (Multiplicative.ofAdd t) * e⁻¹

namespace ExtensionOverAction

variable {ρ : AdditiveAction H T} (X : ExtensionOverAction (E := E) ρ)

/-- The kernel inclusion of an extension over a prescribed action. -/
abbrev inl : Multiplicative T →* E :=
  X.toGroupExtension.inl

/-- The quotient projection of an extension over a prescribed action. -/
abbrev rightHom : E →* H :=
  X.toGroupExtension.rightHom

@[simp]
theorem rightHom_inl (t : Multiplicative T) :
    X.rightHom (X.inl t) = 1 :=
  X.toGroupExtension.rightHom_inl t

end ExtensionOverAction

end WallpaperGroups
