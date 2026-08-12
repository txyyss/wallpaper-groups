import WallpaperGroups.Extensions.Classification
import WallpaperGroups.Extensions.EndpointTransport

set_option linter.style.header false

/-!
# Heterogeneous classification of explicit group extensions

This file combines fixed-action extension classification with transport of the
kernel, quotient, and prescribed action.  The heterogeneous relation is a thin
wrapper: first transport the source extension to the target action, then use
mathlib's existing endpoint-preserving `GroupExtension.Equiv`.

No quotient of all middle-group types and no second fixed-endpoint equivalence
are introduced.
-/

set_option autoImplicit false

namespace WallpaperGroups

variable
    {H T H' T' H'' T'' : Type*}
    [Group H] [AddCommGroup T]
    [Group H'] [AddCommGroup T']
    [Group H''] [AddCommGroup T'']
    {ρ : AdditiveAction H T}
    {ρ' : AdditiveAction H' T'}
    {ρ'' : AdditiveAction H'' T''}

namespace ExtensionOverAction

/-- An equivalence of extensions along an equivalence of their prescribed
actions.

The source extension is relabelled by `a`; the remaining equivalence is exactly
mathlib's endpoint-preserving `GroupExtension.Equiv`.
-/
abbrev EquivAlong
    {E E' : Type*} [Group E] [Group E']
    (X : ExtensionOverAction (E := E) ρ)
    (a : AdditiveAction.Equiv ρ ρ')
    (Y : ExtensionOverAction (E := E') ρ') :=
  (X.transport a).toGroupExtension.Equiv Y.toGroupExtension

namespace EquivAlong

variable
    {E E' E'' : Type*} [Group E] [Group E'] [Group E'']
    {X : ExtensionOverAction (E := E) ρ}
    {Y : ExtensionOverAction (E := E') ρ'}
    {Z : ExtensionOverAction (E := E'') ρ''}
    {a : AdditiveAction.Equiv ρ ρ'}
    {a' : AdditiveAction.Equiv ρ' ρ''}

/-- The kernel square for a heterogeneous extension equivalence, written in
the source kernel coordinate. -/
@[simp]
theorem map_inl (e : X.EquivAlong a Y) (t : T) :
    e (X.inl (Multiplicative.ofAdd t)) =
      Y.inl (Multiplicative.ofAdd (a.kernelEquiv t)) := by
  calc
    e (X.inl (Multiplicative.ofAdd t)) =
        e ((X.transport a).inl
          (Multiplicative.ofAdd (a.kernelEquiv t))) := by simp
    _ = Y.inl (Multiplicative.ofAdd (a.kernelEquiv t)) :=
      GroupExtension.Equiv.map_inl e _

/-- The quotient square for a heterogeneous extension equivalence. -/
@[simp]
theorem rightHom_map (e : X.EquivAlong a Y) (x : E) :
    Y.rightHom (e x) = a.quotientEquiv (X.rightHom x) := by
  calc
    Y.rightHom (e x) = (X.transport a).rightHom x :=
      GroupExtension.Equiv.rightHom_map e x
    _ = a.quotientEquiv (X.rightHom x) := rfl

/-- Regard a fixed-endpoint extension equivalence as an equivalence along the
identity action equivalence. -/
def ofRefl
    {Y₀ : ExtensionOverAction (E := E') ρ}
    (e : X.toGroupExtension.Equiv Y₀.toGroupExtension) :
    X.EquivAlong (AdditiveAction.Equiv.refl ρ) Y₀ where
  __ := e.toMulEquiv
  inl_comm := by
    funext t
    simp
  rightHom_comm := by
    funext x
    simp

/-- Forget identity action transport from a heterogeneous extension
equivalence. -/
def toRefl
    {Y₀ : ExtensionOverAction (E := E') ρ}
    (e : X.EquivAlong (AdditiveAction.Equiv.refl ρ) Y₀) :
    X.toGroupExtension.Equiv Y₀.toGroupExtension where
  __ := e.toMulEquiv
  inl_comm := by
    funext t
    simpa using GroupExtension.Equiv.map_inl e t
  rightHom_comm := by
    funext x
    simp

/-- Along the identity action equivalence, `EquivAlong` is exactly the existing
fixed-endpoint extension equivalence. -/
def reflEquiv
    {Y₀ : ExtensionOverAction (E := E') ρ} :
    X.EquivAlong (AdditiveAction.Equiv.refl ρ) Y₀ ≃
      X.toGroupExtension.Equiv Y₀.toGroupExtension where
  toFun := toRefl
  invFun := ofRefl
  left_inv e := by
    apply DFunLike.coe_injective
    rfl
  right_inv e := by
    apply DFunLike.coe_injective
    rfl

/-- At the proposition level, heterogeneous equivalence along the identity
action equivalence is exactly fixed-endpoint extension equivalence. -/
theorem equivAlong_refl_iff
    {Y₀ : ExtensionOverAction (E := E') ρ} :
    Nonempty
        (X.EquivAlong (AdditiveAction.Equiv.refl ρ) Y₀) ↔
      Nonempty
        (X.toGroupExtension.Equiv Y₀.toGroupExtension) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨toRefl e⟩
  · rintro ⟨e⟩
    exact ⟨ofRefl e⟩

/-- Reverse a heterogeneous extension equivalence, reversing its action
equivalence at the same time. -/
def symm (e : X.EquivAlong a Y) : Y.EquivAlong a.symm X where
  __ := e.toMulEquiv.symm
  inl_comm := by
    funext t
    simp only [Function.comp_apply]
    change
      (GroupExtension.Equiv.symm e)
          ((Y.transport a.symm).inl t) =
        X.inl t
    have hy :
        (Y.transport a.symm).inl t =
          Y.inl
            (Multiplicative.ofAdd
              (a.kernelEquiv t.toAdd)) := by
      simpa [AdditiveAction.Equiv.symm] using
        ExtensionOverAction.transport_inl Y a.symm t.toAdd
    calc
      (GroupExtension.Equiv.symm e)
          ((Y.transport a.symm).inl t) =
          (GroupExtension.Equiv.symm e)
            (Y.inl
              (Multiplicative.ofAdd
                (a.kernelEquiv t.toAdd))) :=
        congrArg (GroupExtension.Equiv.symm e) hy
      _ = (GroupExtension.Equiv.symm e)
          (e (X.inl (Multiplicative.ofAdd t.toAdd))) :=
        congrArg (GroupExtension.Equiv.symm e)
          (map_inl e t.toAdd).symm
      _ = X.inl t := e.toMulEquiv.symm_apply_apply _
  rightHom_comm := by
    funext x
    simp only [Function.comp_apply]
    change
      X.rightHom ((GroupExtension.Equiv.symm e) x) =
        (Y.transport a.symm).rightHom x
    have hx := congrArg a.quotientEquiv.symm
      (GroupExtension.Equiv.rightHom_map
        (GroupExtension.Equiv.symm e) x)
    simpa only [ExtensionOverAction.transport_rightHom,
      MulEquiv.symm_apply_apply, AdditiveAction.Equiv.symm] using hx

/-- Compose heterogeneous extension equivalences together with their action
equivalences. -/
def trans (e : X.EquivAlong a Y) (e' : Y.EquivAlong a' Z) :
    X.EquivAlong (a.trans a') Z where
  __ := e.toMulEquiv.trans e'.toMulEquiv
  inl_comm := by
    funext t
    simp only [Function.comp_apply, MulEquiv.trans_apply]
    change
      e' (e (X.inl
        (Multiplicative.ofAdd
          ((a.trans a').kernelEquiv.symm t)))) =
        Z.inl (Multiplicative.ofAdd t)
    rw [map_inl e, map_inl e']
    apply congrArg Z.inl
    apply congrArg Multiplicative.ofAdd
    exact
      (a.kernelEquiv.trans a'.kernelEquiv).apply_symm_apply t.toAdd
  rightHom_comm := by
    funext x
    simp only [Function.comp_apply, MulEquiv.trans_apply]
    calc
      Z.rightHom (e' (e x)) =
          a'.quotientEquiv (Y.rightHom (e x)) :=
        rightHom_map e' (e x)
      _ = a'.quotientEquiv
          (a.quotientEquiv (X.rightHom x)) := by
        rw [rightHom_map e x]
      _ = ((a.trans a').quotientEquiv) (X.rightHom x) := rfl
      _ = (X.transport (a.trans a')).rightHom x := rfl

end EquivAlong

end ExtensionOverAction

namespace NormalizedSection

variable {E E' : Type*} [Group E] [Group E']

/-- Relabel a normalized section along an equivalence of prescribed actions.

The middle group is unchanged.  Quotient arguments are pulled back through the
inverse quotient equivalence; the endpoint-transported projection then makes
the resulting function a section.
-/
def transport
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (a : AdditiveAction.Equiv ρ ρ') :
    NormalizedSection (X.transport a).toGroupExtension where
  toSection :=
    { toFun := fun h ↦ s (a.quotientEquiv.symm h)
      rightInverse_rightHom := by
        intro h
        simp }
  map_one := by
    simp

/-- Evaluation of a normalized section after action transport. -/
@[simp]
theorem transport_apply
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (a : AdditiveAction.Equiv ρ ρ') (h : H') :
    s.transport X a h = s (a.quotientEquiv.symm h) :=
  rfl

/-- Section factors are natural under simultaneous kernel and quotient
transport. -/
theorem factor_transport
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (a : AdditiveAction.Equiv ρ ρ') (g h : H') :
    factor (s.transport X a) g h =
      a.kernelEquiv
        (factor s (a.quotientEquiv.symm g)
          (a.quotientEquiv.symm h)) := by
  apply (factor_eq_iff (s.transport X a) g h _).2
  rw [ExtensionOverAction.transport_inl]
  simpa using
    (inl_factor s (a.quotientEquiv.symm g)
      (a.quotientEquiv.symm h))

/-- Extracting a cocycle from a transported section is exactly cocycle
transport. -/
theorem toCocycle_transport
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (a : AdditiveAction.Equiv ρ ρ') :
    (s.transport X a).toCocycle (X.transport a) =
      (s.toCocycle X).transport a := by
  ext g h
  exact factor_transport X s a g h

/-- Transport a section along the action endpoints and then through an
`EquivAlong`; its extracted cocycle is the transported source cocycle. -/
theorem toCocycle_equivAlong
    (X : ExtensionOverAction (E := E) ρ)
    (Y : ExtensionOverAction (E := E') ρ')
    (s : NormalizedSection X.toGroupExtension)
    (a : AdditiveAction.Equiv ρ ρ')
    (e : X.EquivAlong a Y) :
    ((s.transport X a).equivComp e).toCocycle Y =
      (s.toCocycle X).transport a := by
  rw [toCocycle_equivComp, toCocycle_transport]

end NormalizedSection

namespace TwistedProduct

/-- Relabel both coordinates of a twisted product along an equivalence of
prescribed actions. -/
def transportMulEquiv
    (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    TwistedProduct c ≃* TwistedProduct (c.transport a) where
  toFun := fun x ↦
    ⟨a.kernelEquiv x.left, a.quotientEquiv x.right⟩
  invFun := fun x ↦
    ⟨a.kernelEquiv.symm x.left, a.quotientEquiv.symm x.right⟩
  left_inv x := by
    ext <;> simp
  right_inv x := by
    ext <;> simp
  map_mul' x y := by
    ext
    · simp only [mul_left, NormalizedCocycle.transport_apply]
      rw [a.kernelEquiv.map_add, a.kernelEquiv.map_add,
        a.intertwines]
      simp
    · simp

/-- Kernel-coordinate evaluation of twisted-product transport. -/
@[simp]
theorem transportMulEquiv_left
    (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ')
    (x : TwistedProduct c) :
    (transportMulEquiv c a x).left = a.kernelEquiv x.left :=
  rfl

/-- Quotient-coordinate evaluation of twisted-product transport. -/
@[simp]
theorem transportMulEquiv_right
    (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ')
    (x : TwistedProduct c) :
    (transportMulEquiv c a x).right = a.quotientEquiv x.right :=
  rfl

/-- Twisted-product coordinate transport, bundled as an `EquivAlong` between
the canonical extensions. -/
def transportExtensionEquivAlong
    (c : NormalizedCocycle ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    (toExtensionOverAction c).EquivAlong a
      (toExtensionOverAction (c.transport a)) where
  __ := transportMulEquiv c a
  inl_comm := by
    funext t
    simp only [Function.comp_apply]
    change
      transportMulEquiv c a
          (TwistedProduct.inl c
            (Multiplicative.ofAdd (a.kernelEquiv.symm t))) =
        TwistedProduct.inl (c.transport a)
          (Multiplicative.ofAdd t)
    ext
    · exact a.kernelEquiv.apply_symm_apply t.toAdd
    · simp
  rightHom_comm := by
    funext x
    simp only [Function.comp_apply]
    rfl

end TwistedProduct

namespace ExtensionOverAction

variable {E E' : Type*} [Group E] [Group E']

/-- Heterogeneous extension equivalence is classified by cocycles after
transporting the source cocycle to the target action.

The statement holds for arbitrary normalized sections.  Section transport
reduces it directly to the fixed-action classifier; hence neither side depends
on a chosen canonical section.
-/
theorem equivAlong_iff_cocycleCohomologous
    (X : ExtensionOverAction (E := E) ρ)
    (Y : ExtensionOverAction (E := E') ρ')
    (a : AdditiveAction.Equiv ρ ρ')
    (s : NormalizedSection X.toGroupExtension)
    (t : NormalizedSection Y.toGroupExtension) :
    Nonempty (X.EquivAlong a Y) ↔
      CocycleCohomologous
        ((s.toCocycle X).transport a)
        (t.toCocycle Y) := by
  simpa [NormalizedSection.toCocycle_transport] using
    ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous
      (X.transport a) Y (s.transport X a) t

end ExtensionOverAction

end WallpaperGroups
