import Mathlib.Algebra.Group.MinimalAxioms
import WallpaperGroups.Extensions.NormalizedCocycle

set_option linter.style.header false

/-!
# Twisted products from normalized cocycles

For an explicit action `ρ` and normalized cocycle `c`, this file constructs the group on `T × H`
with multiplication

```text
(t, g) * (u, h) = (t + ρ(g)(u) + c(g,h), gh).
```

The cocycle identity is used directly in the associativity proof.  The resulting group carries a
canonical mathlib `GroupExtension` and its conjugation action is the prescribed action `ρ`.
-/

set_option autoImplicit false

namespace WallpaperGroups

variable {H T : Type*} [Group H] [AddCommGroup T]
variable {ρ : AdditiveAction H T}

/-- The twisted product attached to a normalized cocycle. -/
structure TwistedProduct (c : NormalizedCocycle ρ) where
  /-- The additive kernel coordinate. -/
  left : T
  /-- The quotient-group coordinate. -/
  right : H

namespace TwistedProduct

variable {c : NormalizedCocycle ρ}

@[ext]
theorem ext {x y : TwistedProduct c}
    (hleft : x.left = y.left) (hright : x.right = y.right) :
    x = y := by
  cases x
  cases y
  simp_all

instance : Mul (TwistedProduct c) where
  mul x y :=
    ⟨x.left + ρ.apply x.right y.left + c x.right y.right,
      x.right * y.right⟩

@[simp]
theorem mul_left (x y : TwistedProduct c) :
    (x * y).left =
      x.left + ρ.apply x.right y.left + c x.right y.right :=
  rfl

@[simp]
theorem mul_right (x y : TwistedProduct c) :
    (x * y).right = x.right * y.right :=
  rfl

instance : One (TwistedProduct c) where
  one := ⟨0, 1⟩

@[simp]
theorem one_left : (1 : TwistedProduct c).left = 0 :=
  rfl

@[simp]
theorem one_right : (1 : TwistedProduct c).right = 1 :=
  rfl

instance : Inv (TwistedProduct c) where
  inv x :=
    ⟨-ρ.apply x.right⁻¹ x.left - c x.right⁻¹ x.right,
      x.right⁻¹⟩

@[simp]
theorem inv_left (x : TwistedProduct c) :
    x⁻¹.left =
      -ρ.apply x.right⁻¹ x.left - c x.right⁻¹ x.right :=
  rfl

@[simp]
theorem inv_right (x : TwistedProduct c) :
    x⁻¹.right = x.right⁻¹ :=
  rfl

instance : Group (TwistedProduct c) :=
  Group.ofLeftAxioms
    (fun x y z ↦ by
      ext
      · simp only [mul_left, mul_right, AdditiveAction.apply_add,
          AdditiveAction.apply_mul]
        calc
          x.left + ρ.apply x.right y.left + c x.right y.right +
                ρ.apply x.right (ρ.apply y.right z.left) +
              c (x.right * y.right) z.right =
            x.left + ρ.apply x.right y.left +
                ρ.apply x.right (ρ.apply y.right z.left) +
              (c x.right y.right + c (x.right * y.right) z.right) := by
                abel
          _ = x.left + ρ.apply x.right y.left +
                ρ.apply x.right (ρ.apply y.right z.left) +
              (ρ.apply x.right (c y.right z.right) +
                c x.right (y.right * z.right)) := by
                  rw [c.cocycle]
          _ = x.left +
                (ρ.apply x.right y.left +
                  ρ.apply x.right (ρ.apply y.right z.left) +
                  ρ.apply x.right (c y.right z.right)) +
              c x.right (y.right * z.right) := by
                abel
      · simp only [mul_right, mul_assoc])
    (fun x ↦ by
      ext
      · simp
      · simp)
    (fun x ↦ by
      ext
      · simp only [inv_left, mul_left, inv_right, one_left]
        abel
      · simp)

/-- Associativity of twisted multiplication, obtained from the cocycle identity. -/
theorem associative (x y z : TwistedProduct c) :
    (x * y) * z = x * (y * z) :=
  mul_assoc x y z

/-- The canonical inclusion of the additive kernel into a twisted product. -/
def inl (c : NormalizedCocycle ρ) :
    Multiplicative T →* TwistedProduct c where
  toFun t := ⟨t.toAdd, 1⟩
  map_one' := by
    ext <;> simp
  map_mul' t u := by
    ext <;> simp

@[simp]
theorem inl_left (c : NormalizedCocycle ρ) (t : Multiplicative T) :
    (inl c t).left = t.toAdd :=
  rfl

@[simp]
theorem inl_right (c : NormalizedCocycle ρ) (t : Multiplicative T) :
    (inl c t).right = 1 :=
  rfl

/-- The canonical projection of a twisted product to its quotient coordinate. -/
def rightHom (c : NormalizedCocycle ρ) :
    TwistedProduct c →* H where
  toFun := TwistedProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem rightHom_apply (c : NormalizedCocycle ρ) (x : TwistedProduct c) :
    rightHom c x = x.right :=
  rfl

theorem inl_injective (c : NormalizedCocycle ρ) :
    Function.Injective (inl c) := by
  intro t u h
  exact Multiplicative.toAdd.injective (congrArg TwistedProduct.left h)

/-- The canonical short exact sequence associated to a twisted product. -/
def toGroupExtension (c : NormalizedCocycle ρ) :
    GroupExtension (Multiplicative T) (TwistedProduct c) H where
  inl := inl c
  rightHom := rightHom c
  inl_injective := inl_injective c
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      simp
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      refine ⟨Multiplicative.ofAdd x.left, ?_⟩
      ext
      · rfl
      · simpa using hx.symm
  rightHom_surjective := by
    intro h
    exact ⟨⟨0, h⟩, rfl⟩

@[simp]
theorem toGroupExtension_inl (c : NormalizedCocycle ρ)
    (t : Multiplicative T) :
    (toGroupExtension c).inl t = inl c t :=
  rfl

@[simp]
theorem toGroupExtension_rightHom (c : NormalizedCocycle ρ)
    (x : TwistedProduct c) :
    (toGroupExtension c).rightHom x = x.right :=
  rfl

/-- Moving a kernel element left across a twisted-product element applies the quotient action. -/
theorem mul_inl (c : NormalizedCocycle ρ)
    (x : TwistedProduct c) (t : T) :
    x * inl c (Multiplicative.ofAdd t) =
      inl c (Multiplicative.ofAdd (ρ.apply x.right t)) * x := by
  ext
  · simp
    abel
  · simp

/-- The canonical twisted-product extension realizes the prescribed action by conjugation. -/
def toExtensionOverAction (c : NormalizedCocycle ρ) :
    ExtensionOverAction (E := TwistedProduct c) ρ where
  toGroupExtension := toGroupExtension c
  conjugation_inl := by
    intro x t
    have h := congrArg (fun y : TwistedProduct c ↦ y * x⁻¹) (mul_inl c x t)
    simpa [mul_assoc] using h.symm

@[simp]
theorem toExtensionOverAction_inl (c : NormalizedCocycle ρ)
    (t : Multiplicative T) :
    (toExtensionOverAction c).toGroupExtension.inl t = inl c t :=
  rfl

@[simp]
theorem toExtensionOverAction_rightHom (c : NormalizedCocycle ρ)
    (x : TwistedProduct c) :
    (toExtensionOverAction c).toGroupExtension.rightHom x = x.right :=
  rfl

/-- Coordinate change between twisted products whose cocycles differ by the coboundary of `b`.

The sign matches the convention `c.changeBy b = c + δb`: the kernel coordinate changes by
`t ↦ t - b(g)`.
-/
def changeByMulEquiv (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) :
    TwistedProduct c ≃* TwistedProduct (c.changeBy b) where
  toFun x := ⟨x.left - b x.right, x.right⟩
  invFun x := ⟨x.left + b x.right, x.right⟩
  left_inv x := by
    ext
    · simp
    · rfl
  right_inv x := by
    ext
    · simp
    · rfl
  map_mul' x y := by
    ext
    · simp only [mul_left, NormalizedCocycle.changeBy_apply,
        NormalizedCochain.coboundary_apply, AdditiveAction.apply_sub]
      abel
    · rfl

@[simp]
theorem changeByMulEquiv_left (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) (x : TwistedProduct c) :
    (changeByMulEquiv c b x).left = x.left - b x.right :=
  rfl

@[simp]
theorem changeByMulEquiv_right (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) (x : TwistedProduct c) :
    (changeByMulEquiv c b x).right = x.right :=
  rfl

/-- Coboundary coordinate change fixes the kernel inclusion. -/
@[simp]
theorem changeByMulEquiv_inl (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) (t : Multiplicative T) :
    changeByMulEquiv c b (inl c t) =
      inl (c.changeBy b) t := by
  ext <;> simp

/-- Coboundary coordinate change commutes with the quotient projection. -/
@[simp]
theorem rightHom_changeByMulEquiv (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) (x : TwistedProduct c) :
    rightHom (c.changeBy b) (changeByMulEquiv c b x) =
      rightHom c x :=
  rfl

end TwistedProduct

end WallpaperGroups
