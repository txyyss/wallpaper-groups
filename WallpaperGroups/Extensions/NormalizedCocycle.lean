import Mathlib.Tactic.Abel
import WallpaperGroups.Extensions.Action

set_option linter.style.header false

/-!
# Normalized cocycles and explicit coboundaries

This file defines the explicit, dimension-independent cochain layer used by the project.  It does
not import mathlib's homological group-cohomology API.  For a prescribed additive action `ρ`, the
cocycle convention is

```text
c(g,h) + c(gh,k) = g • c(h,k) + c(g,hk),
```

and a normalized section change by `b` changes the factor by

```text
δb(g,h) = b(g) + g • b(h) - b(gh).
```
-/

set_option autoImplicit false

namespace WallpaperGroups

variable {H T : Type*} [Group H] [AddCommGroup T]

/-- A normalized additive `2`-cocycle for an explicit action. -/
structure NormalizedCocycle (ρ : AdditiveAction H T) where
  /-- The underlying factor function. -/
  toFun : H → H → T
  /-- Normalization in the left argument. -/
  one_left : ∀ h : H, toFun 1 h = 0
  /-- Normalization in the right argument. -/
  one_right : ∀ g : H, toFun g 1 = 0
  /-- The inhomogeneous left-action cocycle identity. -/
  cocycle :
    ∀ g h k : H,
      toFun g h + toFun (g * h) k =
        ρ.apply g (toFun h k) + toFun g (h * k)

namespace NormalizedCocycle

variable {ρ : AdditiveAction H T}

instance : CoeFun (NormalizedCocycle ρ) (fun _ ↦ H → H → T) :=
  ⟨NormalizedCocycle.toFun⟩

@[simp]
theorem one_left_apply (c : NormalizedCocycle ρ) (h : H) :
    c 1 h = 0 :=
  c.one_left h

@[simp]
theorem one_right_apply (c : NormalizedCocycle ρ) (g : H) :
    c g 1 = 0 :=
  c.one_right g

@[ext]
theorem ext {c d : NormalizedCocycle ρ}
    (h : ∀ g k : H, c g k = d g k) : c = d := by
  cases c
  cases d
  congr
  funext g k
  exact h g k

/-- The normalized zero cocycle. -/
def zero (ρ : AdditiveAction H T) : NormalizedCocycle ρ where
  toFun := fun _ _ ↦ 0
  one_left := fun _ ↦ rfl
  one_right := fun _ ↦ rfl
  cocycle := by simp

@[simp]
theorem zero_apply (ρ : AdditiveAction H T) (g h : H) :
    zero ρ g h = 0 :=
  rfl

end NormalizedCocycle

/-- A normalized additive `1`-cochain. -/
structure NormalizedCochain (H T : Type*) [Group H] [AddCommGroup T] where
  /-- The underlying function. -/
  toFun : H → T
  /-- Normalization at the identity. -/
  map_one : toFun 1 = 0

namespace NormalizedCochain

variable {ρ : AdditiveAction H T}

instance : CoeFun (NormalizedCochain H T) (fun _ ↦ H → T) :=
  ⟨NormalizedCochain.toFun⟩

@[simp]
theorem apply_one (b : NormalizedCochain H T) : b 1 = 0 :=
  b.map_one

@[ext]
theorem ext {b d : NormalizedCochain H T}
    (h : ∀ g : H, b g = d g) : b = d := by
  cases b
  cases d
  congr
  funext g
  exact h g

/-- The zero normalized cochain. -/
def zero : NormalizedCochain H T where
  toFun := fun _ ↦ 0
  map_one := rfl

@[simp]
theorem zero_apply (g : H) : (zero : NormalizedCochain H T) g = 0 :=
  rfl

/-- Pointwise addition of normalized cochains. -/
def add (b d : NormalizedCochain H T) : NormalizedCochain H T where
  toFun := fun g ↦ b g + d g
  map_one := by simp

@[simp]
theorem add_apply (b d : NormalizedCochain H T) (g : H) :
    b.add d g = b g + d g :=
  rfl

/-- Pointwise negation of a normalized cochain. -/
def neg (b : NormalizedCochain H T) : NormalizedCochain H T where
  toFun := fun g ↦ -b g
  map_one := by simp

@[simp]
theorem neg_apply (b : NormalizedCochain H T) (g : H) :
    b.neg g = -b g :=
  rfl

/-- The explicit coboundary of a normalized `1`-cochain. -/
def coboundary (ρ : AdditiveAction H T) (b : NormalizedCochain H T) :
    NormalizedCocycle ρ where
  toFun := fun g h ↦ b g + ρ.apply g (b h) - b (g * h)
  one_left := by
    intro h
    simp
  one_right := by
    intro g
    simp
  cocycle := by
    intro g h k
    rw [AdditiveAction.apply_sub, AdditiveAction.apply_add,
      AdditiveAction.apply_mul, mul_assoc]
    abel

@[simp]
theorem coboundary_apply (b : NormalizedCochain H T) (g h : H) :
    b.coboundary ρ g h = b g + ρ.apply g (b h) - b (g * h) :=
  rfl

end NormalizedCochain

namespace NormalizedCocycle

variable {ρ : AdditiveAction H T}

/-- Change a cocycle by the explicit coboundary of a normalized cochain. -/
def changeBy (c : NormalizedCocycle ρ) (b : NormalizedCochain H T) :
    NormalizedCocycle ρ where
  toFun := fun g h ↦ c g h + b.coboundary ρ g h
  one_left := by
    intro h
    simp
  one_right := by
    intro g
    simp
  cocycle := by
    intro g h k
    have hc := c.cocycle g h k
    have hb := (b.coboundary ρ).cocycle g h k
    calc
      (c g h + b.coboundary ρ g h) +
          (c (g * h) k + b.coboundary ρ (g * h) k) =
        (c g h + c (g * h) k) +
          (b.coboundary ρ g h + b.coboundary ρ (g * h) k) := by
            abel
      _ = (ρ.apply g (c h k) + c g (h * k)) +
          (ρ.apply g (b.coboundary ρ h k) +
            b.coboundary ρ g (h * k)) := by
              rw [hc, hb]
      _ = ρ.apply g (c h k + b.coboundary ρ h k) +
          (c g (h * k) + b.coboundary ρ g (h * k)) := by
            rw [AdditiveAction.apply_add]
            abel

@[simp]
theorem changeBy_apply (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) (g h : H) :
    c.changeBy b g h = c g h + b.coboundary ρ g h :=
  rfl

theorem changeBy_zero (c : NormalizedCocycle ρ) :
    c.changeBy NormalizedCochain.zero = c := by
  ext g h
  simp [changeBy, NormalizedCochain.coboundary]

theorem changeBy_add (c : NormalizedCocycle ρ)
    (b d : NormalizedCochain H T) :
    (c.changeBy b).changeBy d = c.changeBy (b.add d) := by
  ext g h
  simp [changeBy, NormalizedCochain.coboundary, AdditiveAction.apply_add]
  abel

theorem changeBy_neg (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) :
    (c.changeBy b).changeBy b.neg = c := by
  rw [changeBy_add]
  ext g h
  simp [changeBy, NormalizedCochain.coboundary]

end NormalizedCocycle

/-- Two normalized cocycles are cohomologous when they differ by the explicit coboundary of a
normalized cochain. -/
def CocycleCohomologous {ρ : AdditiveAction H T}
    (c d : NormalizedCocycle ρ) : Prop :=
  ∃ b : NormalizedCochain H T, d = c.changeBy b

namespace CocycleCohomologous

variable {ρ : AdditiveAction H T}

theorem refl (c : NormalizedCocycle ρ) :
    CocycleCohomologous c c :=
  ⟨NormalizedCochain.zero, c.changeBy_zero.symm⟩

theorem symm {c d : NormalizedCocycle ρ}
    (h : CocycleCohomologous c d) :
    CocycleCohomologous d c := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨b.neg, (c.changeBy_neg b).symm⟩

theorem trans {c d e : NormalizedCocycle ρ}
    (hcd : CocycleCohomologous c d)
    (hde : CocycleCohomologous d e) :
    CocycleCohomologous c e := by
  obtain ⟨b, rfl⟩ := hcd
  obtain ⟨d, rfl⟩ := hde
  exact ⟨b.add d, c.changeBy_add b d⟩

/-- The explicit cocycle/coboundary equivalence relation. -/
def setoid (ρ : AdditiveAction H T) : Setoid (NormalizedCocycle ρ) where
  r := CocycleCohomologous
  iseqv := ⟨refl, symm, trans⟩

end CocycleCohomologous

end WallpaperGroups
