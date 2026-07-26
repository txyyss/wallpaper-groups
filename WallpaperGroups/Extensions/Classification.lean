import WallpaperGroups.Extensions.Section

set_option linter.style.header false

/-!
# Fixed-action extension equivalence

This file completes the fixed-endpoint layer of the explicit extension theory.  A coboundary
coordinate change is bundled using mathlib's existing `GroupExtension.Equiv`, normalized sections
are transported through that same notion of equivalence, and every extension with a normalized
section is reconstructed from its extracted twisted product.

For a fixed explicit action, the resulting pairwise theorem says that the canonical extensions of
two normalized cocycles are endpoint-preservingly equivalent exactly when the cocycles differ by
an explicit normalized coboundary.  No quotient over varying middle-group types and no
group-cohomology library is used.
-/

set_option autoImplicit false

namespace WallpaperGroups

variable {H T : Type*} [Group H] [AddCommGroup T]
variable {ρ : AdditiveAction H T}

namespace TwistedProduct

/-- A coboundary coordinate change, bundled as an endpoint-preserving extension equivalence. -/
def changeByExtensionEquiv (c : NormalizedCocycle ρ)
    (b : NormalizedCochain H T) :
    (toGroupExtension c).Equiv (toGroupExtension (c.changeBy b)) where
  __ := changeByMulEquiv c b
  inl_comm := by
    funext t
    exact changeByMulEquiv_inl c b t
  rightHom_comm := by
    funext x
    exact rightHom_changeByMulEquiv c b x

end TwistedProduct

namespace NormalizedSection

section Transport

variable {N E E' : Type*}
variable [Group N] [Group E] [Group E']
variable {S : GroupExtension N E H} {S' : GroupExtension N E' H}

/-- Transport a normalized section through an endpoint-preserving extension equivalence. -/
def equivComp (s : NormalizedSection S) (e : S.Equiv S') :
    NormalizedSection S' where
  toSection := s.toSection.equivComp e
  map_one := by
    change e (s 1) = 1
    simp

@[simp]
theorem equivComp_apply (s : NormalizedSection S) (e : S.Equiv S') (h : H) :
    s.equivComp e h = e (s h) :=
  rfl

end Transport

section FactorNaturality

variable {E E' : Type*} [Group E] [Group E']
variable {S : GroupExtension (Multiplicative T) E H}
variable {S' : GroupExtension (Multiplicative T) E' H}

/-- Transport through an extension equivalence preserves a normalized section's factor exactly. -/
theorem factor_equivComp (s : NormalizedSection S) (e : S.Equiv S')
    (g h : H) :
    factor (s.equivComp e) g h = factor s g h := by
  apply Multiplicative.ofAdd.injective
  apply S'.inl_injective
  rw [inl_factor, ← e.map_inl, inl_factor]
  simp

/-- Extracted cocycles are exactly natural under endpoint-preserving extension equivalences. -/
theorem toCocycle_equivComp
    (X : ExtensionOverAction (E := E) ρ)
    (Y : ExtensionOverAction (E := E') ρ)
    (s : NormalizedSection X.toGroupExtension)
    (e : X.toGroupExtension.Equiv Y.toGroupExtension) :
    (s.equivComp e).toCocycle Y = s.toCocycle X := by
  ext g h
  exact factor_equivComp s e g h

end FactorNaturality

section Reconstruction

variable {E : Type*} [Group E]

/-- The normal-form homomorphism from the cocycle twisted product back to its source extension.

The normal form sends `(t, h)` to `inl(t) * s(h)`.  Multiplicativity is precisely the combination
of the prescribed conjugation action and the factor identity for `s`.
-/
noncomputable def normalFormHom
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension) :
    TwistedProduct (s.toCocycle X) →* E where
  toFun := fun x ↦ X.inl (Multiplicative.ofAdd x.left) * s x.right
  map_one' := by
    simp
  map_mul' := by
    intro x y
    change
      X.inl (Multiplicative.ofAdd
          (x.left + ρ.apply x.right y.left + factor s x.right y.right)) *
          s (x.right * y.right) =
        (X.inl (Multiplicative.ofAdd x.left) * s x.right) *
          (X.inl (Multiplicative.ofAdd y.left) * s y.right)
    rw [ofAdd_add, ofAdd_add, map_mul, map_mul]
    rw [conjugation_inl X s, inl_factor]
    group

@[simp]
theorem normalFormHom_apply
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (x : TwistedProduct (s.toCocycle X)) :
    normalFormHom X s x =
      X.inl (Multiplicative.ofAdd x.left) * s x.right :=
  rfl

@[simp]
theorem normalFormHom_inl
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (t : Multiplicative T) :
    normalFormHom X s
        (TwistedProduct.inl (s.toCocycle X) t) =
      X.inl t := by
  simp

@[simp]
theorem rightHom_normalFormHom
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (x : TwistedProduct (s.toCocycle X)) :
    X.rightHom (normalFormHom X s x) =
      TwistedProduct.rightHom (s.toCocycle X) x := by
  simp

/-- Reconstruction from a normalized section as an endpoint-preserving extension equivalence. -/
noncomputable def twistedProductExtensionEquiv
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension) :
    (TwistedProduct.toGroupExtension (s.toCocycle X)).Equiv
      X.toGroupExtension :=
  GroupExtension.Equiv.ofMonoidHom
    (normalFormHom X s)
    (by
      ext t
      simp)
    (by
      ext x
      simp)

@[simp]
theorem twistedProductExtensionEquiv_apply
    (X : ExtensionOverAction (E := E) ρ)
    (s : NormalizedSection X.toGroupExtension)
    (x : TwistedProduct (s.toCocycle X)) :
    twistedProductExtensionEquiv X s x =
      X.inl (Multiplicative.ofAdd x.left) * s x.right :=
  rfl

end Reconstruction

end NormalizedSection

namespace TwistedProduct

/-- For a fixed action, canonical twisted-product extensions are endpoint-preservingly equivalent
exactly when their normalized cocycles differ by an explicit coboundary. -/
theorem extensionEquiv_iff_cocycleCohomologous
    (c d : NormalizedCocycle ρ) :
    Nonempty ((toGroupExtension c).Equiv (toGroupExtension d)) ↔
      CocycleCohomologous c d := by
  constructor
  · rintro ⟨e⟩
    let s : NormalizedSection (toExtensionOverAction d).toGroupExtension :=
      (canonicalSection c).equivComp e
    refine ⟨NormalizedSection.differenceCochain (canonicalSection d) s, ?_⟩
    calc
      d =
          (canonicalSection d).toCocycle
            (toExtensionOverAction d) :=
        (canonicalSection_toCocycle d).symm
      _ =
          (s.toCocycle (toExtensionOverAction d)).changeBy
            (NormalizedSection.differenceCochain (canonicalSection d) s) :=
        NormalizedSection.toCocycle_change
          (toExtensionOverAction d) (canonicalSection d) s
      _ =
          c.changeBy
            (NormalizedSection.differenceCochain (canonicalSection d) s) := by
        rw [NormalizedSection.toCocycle_equivComp
          (toExtensionOverAction c) (toExtensionOverAction d)
          (canonicalSection c) e, canonicalSection_toCocycle]
  · rintro ⟨b, rfl⟩
    exact ⟨changeByExtensionEquiv c b⟩

end TwistedProduct

end WallpaperGroups
