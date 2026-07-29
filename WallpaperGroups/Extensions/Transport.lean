import WallpaperGroups.Extensions.NormalizedCocycle

set_option linter.style.header false

/-!
# Transport of explicit actions, cochains, and cocycles

This file supplies the dimension-independent transport layer for the explicit cocycle API.
Transport is directed from a source action to a target action.  Functions on the quotient are
precomposed with the inverse quotient equivalence, while their values are mapped forward by the
kernel equivalence.

Only action and cocycle data are transported here.  Transport of group-extension endpoints is a
separate layer.
-/

set_option autoImplicit false

namespace WallpaperGroups

namespace AdditiveAction

/-- An equivalence between two explicit additive actions.

The additive kernel and quotient group may both change.  The `intertwines` field states that the
two endpoint equivalences identify the prescribed actions.
-/
structure Equiv
    {H T H' T' : Type*}
    [Group H] [AddCommGroup T] [Group H'] [AddCommGroup T']
    (ρ : AdditiveAction H T) (ρ' : AdditiveAction H' T') where
  /-- The additive equivalence between the kernel groups. -/
  kernelEquiv : T ≃+ T'
  /-- The multiplicative equivalence between the quotient groups. -/
  quotientEquiv : H ≃* H'
  /-- The kernel equivalence intertwines the two quotient actions. -/
  intertwines :
    ∀ (h : H) (t : T),
      kernelEquiv (ρ.apply h t) =
        ρ'.apply (quotientEquiv h) (kernelEquiv t)

namespace Equiv

variable
    {H T H' T' H'' T'' : Type*}
    [Group H] [AddCommGroup T]
    [Group H'] [AddCommGroup T']
    [Group H''] [AddCommGroup T'']
    {ρ : AdditiveAction H T}
    {ρ' : AdditiveAction H' T'}
    {ρ'' : AdditiveAction H'' T''}

/-- The identity equivalence of an explicit additive action. -/
protected def refl (ρ : AdditiveAction H T) : Equiv ρ ρ where
  kernelEquiv := AddEquiv.refl T
  quotientEquiv := MulEquiv.refl H
  intertwines := by
    intro h t
    rfl

/-- Reverse an equivalence of explicit additive actions. -/
protected def symm (a : Equiv ρ ρ') : Equiv ρ' ρ where
  kernelEquiv := a.kernelEquiv.symm
  quotientEquiv := a.quotientEquiv.symm
  intertwines := by
    intro h t
    apply a.kernelEquiv.injective
    simpa using
      (a.intertwines (a.quotientEquiv.symm h) (a.kernelEquiv.symm t)).symm

/-- Compose equivalences of explicit additive actions. -/
protected def trans (a : Equiv ρ ρ') (a' : Equiv ρ' ρ'') : Equiv ρ ρ'' where
  kernelEquiv := a.kernelEquiv.trans a'.kernelEquiv
  quotientEquiv := a.quotientEquiv.trans a'.quotientEquiv
  intertwines := by
    intro h t
    change a'.kernelEquiv (a.kernelEquiv (ρ.apply h t)) =
      ρ''.apply (a'.quotientEquiv (a.quotientEquiv h))
        (a'.kernelEquiv (a.kernelEquiv t))
    rw [a.intertwines, a'.intertwines]

end Equiv

end AdditiveAction

variable
    {H T H' T' H'' T'' : Type*}
    [Group H] [AddCommGroup T]
    [Group H'] [AddCommGroup T']
    [Group H''] [AddCommGroup T'']
    {ρ : AdditiveAction H T}
    {ρ' : AdditiveAction H' T'}
    {ρ'' : AdditiveAction H'' T''}

namespace NormalizedCochain

/-- Transport a normalized cochain forward along an equivalence of actions. -/
def transport (b : NormalizedCochain H T) (a : AdditiveAction.Equiv ρ ρ') :
    NormalizedCochain H' T' where
  toFun := fun h ↦ a.kernelEquiv (b (a.quotientEquiv.symm h))
  map_one := by
    simp

@[simp]
theorem transport_apply (b : NormalizedCochain H T)
    (a : AdditiveAction.Equiv ρ ρ') (h : H') :
    b.transport a h = a.kernelEquiv (b (a.quotientEquiv.symm h)) :=
  rfl

/-- Transporting a normalized cochain along the identity action equivalence does nothing. -/
@[simp]
theorem transport_refl (b : NormalizedCochain H T) :
    b.transport (AdditiveAction.Equiv.refl ρ) = b := by
  ext h
  rfl

/-- Transport of normalized cochains respects composition of action equivalences. -/
theorem transport_trans (b : NormalizedCochain H T)
    (a : AdditiveAction.Equiv ρ ρ') (a' : AdditiveAction.Equiv ρ' ρ'') :
    (b.transport a).transport a' = b.transport (a.trans a') := by
  ext h
  rfl

/-- Transporting a normalized cochain forward and then backward is the identity. -/
@[simp]
theorem transport_symm (b : NormalizedCochain H T)
    (a : AdditiveAction.Equiv ρ ρ') :
    (b.transport a).transport a.symm = b := by
  ext h
  simp [AdditiveAction.Equiv.symm]

/-- Transporting a normalized cochain backward and then forward is the identity. -/
@[simp]
theorem symm_transport (b : NormalizedCochain H' T')
    (a : AdditiveAction.Equiv ρ ρ') :
    (b.transport a.symm).transport a = b := by
  ext h
  simp [AdditiveAction.Equiv.symm]

end NormalizedCochain

namespace NormalizedCocycle

/-- Transport a normalized cocycle forward along an equivalence of actions. -/
def transport (c : NormalizedCocycle ρ) (a : AdditiveAction.Equiv ρ ρ') :
    NormalizedCocycle ρ' where
  toFun := fun g h ↦
    a.kernelEquiv
      (c (a.quotientEquiv.symm g) (a.quotientEquiv.symm h))
  one_left := by
    intro h
    simp
  one_right := by
    intro g
    simp
  cocycle := by
    intro g h k
    simp only [map_mul]
    rw [← a.kernelEquiv.map_add, c.cocycle, a.kernelEquiv.map_add, a.intertwines]
    simp

@[simp]
theorem transport_apply (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ') (g h : H') :
    c.transport a g h =
      a.kernelEquiv
        (c (a.quotientEquiv.symm g) (a.quotientEquiv.symm h)) :=
  rfl

/-- Transporting a normalized cocycle along the identity action equivalence does nothing. -/
@[simp]
theorem transport_refl (c : NormalizedCocycle ρ) :
    c.transport (AdditiveAction.Equiv.refl ρ) = c := by
  ext g h
  rfl

/-- Transport of normalized cocycles respects composition of action equivalences. -/
theorem transport_trans (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ') (a' : AdditiveAction.Equiv ρ' ρ'') :
    (c.transport a).transport a' = c.transport (a.trans a') := by
  ext g h
  rfl

/-- Transporting a normalized cocycle forward and then backward is the identity. -/
@[simp]
theorem transport_symm (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    (c.transport a).transport a.symm = c := by
  ext g h
  simp [AdditiveAction.Equiv.symm]

/-- Transporting a normalized cocycle backward and then forward is the identity. -/
@[simp]
theorem symm_transport (c : NormalizedCocycle ρ')
    (a : AdditiveAction.Equiv ρ ρ') :
    (c.transport a.symm).transport a = c := by
  ext g h
  simp [AdditiveAction.Equiv.symm]

end NormalizedCocycle

namespace NormalizedCochain

/-- Coboundaries commute exactly with transport along an action equivalence. -/
theorem coboundary_transport (b : NormalizedCochain H T)
    (a : AdditiveAction.Equiv ρ ρ') :
    (b.coboundary ρ).transport a =
      (b.transport a).coboundary ρ' := by
  ext g h
  simp only [NormalizedCocycle.transport_apply, coboundary_apply, transport_apply]
  rw [a.kernelEquiv.map_sub, a.kernelEquiv.map_add, a.intertwines]
  simp

end NormalizedCochain

namespace NormalizedCocycle

/-- Changing a cocycle by a coboundary commutes exactly with action transport. -/
theorem changeBy_transport (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) (a : AdditiveAction.Equiv ρ ρ') :
    (c.changeBy b).transport a =
      (c.transport a).changeBy (b.transport a) := by
  ext g h
  simp only [transport_apply, changeBy_apply]
  rw [a.kernelEquiv.map_add]
  have hb := congrArg
    (fun z : NormalizedCocycle ρ' ↦ z g h)
    (NormalizedCochain.coboundary_transport b a)
  exact congrArg (fun z ↦ a.kernelEquiv (c
    (a.quotientEquiv.symm g) (a.quotientEquiv.symm h)) + z) hb

end NormalizedCocycle

namespace CocycleCohomologous

/-- Cohomologous cocycles remain cohomologous after transport. -/
theorem transport (a : AdditiveAction.Equiv ρ ρ')
    {c d : NormalizedCocycle ρ} (h : CocycleCohomologous c d) :
    CocycleCohomologous (c.transport a) (d.transport a) := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨b.transport a, c.changeBy_transport b a⟩

/-- Cocycle cohomology is invariant under an equivalence of explicit actions. -/
theorem transport_iff (a : AdditiveAction.Equiv ρ ρ')
    (c d : NormalizedCocycle ρ) :
    CocycleCohomologous c d ↔
      CocycleCohomologous (c.transport a) (d.transport a) := by
  constructor
  · exact transport a
  · intro h
    simpa using transport a.symm h

end CocycleCohomologous

end WallpaperGroups
