import WallpaperGroups.Extensions.Transport

set_option linter.style.header false

/-!
# Transport of group-extension endpoints

This file connects equivalences of explicit additive actions to mathlib's
`GroupExtension` short exact sequences.  Endpoint transport changes only the
kernel and quotient labels; the middle group and all of its multiplication
remain unchanged.

The construction is deliberately separate from heterogeneous extension
classification.  It does not introduce a second notion of extension
equivalence.
-/

set_option autoImplicit false

namespace WallpaperGroups

namespace GroupExtension

variable
    {N N' N'' E H H' H'' : Type*}
    [Group N] [Group N'] [Group N''] [Group E]
    [Group H] [Group H'] [Group H'']

/-- Relabel the quotient endpoint of a group extension along a group equivalence.

The middle group and kernel inclusion are unchanged; the quotient projection is
postcomposed with the supplied equivalence.
-/
def relabelQuotient (S : GroupExtension N E H) (e : H ≃* H') :
    GroupExtension N E H' where
  inl := S.inl
  rightHom := e.toMonoidHom.comp S.rightHom
  inl_injective := S.inl_injective
  range_inl_eq_ker_rightHom := by
    calc
      S.inl.range = S.rightHom.ker := S.range_inl_eq_ker_rightHom
      _ = (e.toMonoidHom.comp S.rightHom).ker := by
        ext x
        simp [MonoidHom.mem_ker]
  rightHom_surjective := e.surjective.comp S.rightHom_surjective

/-- Relabelling the quotient leaves the kernel inclusion unchanged. -/
@[simp]
theorem relabelQuotient_inl (S : GroupExtension N E H) (e : H ≃* H') (n : N) :
    (relabelQuotient S e).inl n = S.inl n :=
  rfl

/-- The relabelled quotient projection is the old projection followed by the equivalence. -/
@[simp]
theorem relabelQuotient_rightHom
    (S : GroupExtension N E H) (e : H ≃* H') (x : E) :
    (relabelQuotient S e).rightHom x = e (S.rightHom x) :=
  rfl

/-- Transport both endpoints of a group extension while preserving its middle group.

The kernel equivalence is directed from the old kernel to the new kernel, so
the new inclusion precomposes the old inclusion with its inverse.  The quotient
projection is postcomposed with the quotient equivalence.
-/
def transportEndpoints (S : GroupExtension N E H)
    (eN : N ≃* N') (eH : H ≃* H') :
    GroupExtension N' E H' :=
  relabelQuotient (relabelKernel S eN.symm) eH

/-- Endpoint transport sends a new kernel coordinate through the inverse kernel equivalence. -/
@[simp]
theorem transportEndpoints_inl
    (S : GroupExtension N E H) (eN : N ≃* N') (eH : H ≃* H') (n : N') :
    (transportEndpoints S eN eH).inl n = S.inl (eN.symm n) :=
  rfl

/-- Endpoint transport sends the old quotient coordinate through the quotient equivalence. -/
@[simp]
theorem transportEndpoints_rightHom
    (S : GroupExtension N E H) (eN : N ≃* N') (eH : H ≃* H') (x : E) :
    (transportEndpoints S eN eH).rightHom x = eH (S.rightHom x) :=
  rfl

private theorem ext_of_maps
    {S S' : GroupExtension N E H}
    (hinl : S.inl = S'.inl) (hrightHom : S.rightHom = S'.rightHom) :
    S = S' := by
  cases S
  cases S'
  cases hinl
  cases hrightHom
  rfl

/-- Transporting extension endpoints along identity equivalences is the identity. -/
@[simp]
theorem transportEndpoints_refl (S : GroupExtension N E H) :
    transportEndpoints S (MulEquiv.refl N) (MulEquiv.refl H) = S := by
  apply ext_of_maps
  · ext n
    rfl
  · ext x
    rfl

/-- Endpoint transport respects composition of kernel and quotient equivalences. -/
theorem transportEndpoints_trans
    (S : GroupExtension N E H)
    (eN : N ≃* N') (eH : H ≃* H')
    (eN' : N' ≃* N'') (eH' : H' ≃* H'') :
    transportEndpoints (transportEndpoints S eN eH) eN' eH' =
      transportEndpoints S (eN.trans eN') (eH.trans eH') := by
  apply ext_of_maps
  · ext n
    rfl
  · ext x
    rfl

/-- Transporting extension endpoints forward and then backward recovers the extension. -/
@[simp]
theorem transportEndpoints_symm
    (S : GroupExtension N E H) (eN : N ≃* N') (eH : H ≃* H') :
    transportEndpoints (transportEndpoints S eN eH) eN.symm eH.symm = S := by
  apply ext_of_maps
  · ext n
    simp
  · ext x
    simp

/-- Transporting extension endpoints backward and then forward recovers the extension. -/
@[simp]
theorem symm_transportEndpoints
    (S : GroupExtension N' E H') (eN : N ≃* N') (eH : H ≃* H') :
    transportEndpoints (transportEndpoints S eN.symm eH.symm) eN eH = S := by
  apply ext_of_maps
  · ext n
    simp
  · ext x
    simp

end GroupExtension

variable
    {H T H' T' H'' T'' E : Type*}
    [Group H] [AddCommGroup T]
    [Group H'] [AddCommGroup T']
    [Group H''] [AddCommGroup T'']
    [Group E]
    {ρ : AdditiveAction H T}
    {ρ' : AdditiveAction H' T'}
    {ρ'' : AdditiveAction H'' T''}

namespace ExtensionOverAction

/-- Transport an extension over an explicit action along an equivalence of actions.

The middle group is retained verbatim.  Its kernel and quotient maps are merely
relabelled by the endpoint equivalences, and action compatibility follows from
the intertwining field of `AdditiveAction.Equiv`.
-/
def transport (X : ExtensionOverAction (E := E) ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    ExtensionOverAction (E := E) ρ' where
  toGroupExtension :=
    GroupExtension.transportEndpoints X.toGroupExtension
      (AddEquiv.toMultiplicative a.kernelEquiv) a.quotientEquiv
  conjugation_inl := by
    intro e t
    change
      X.inl
          (Multiplicative.ofAdd
            (a.kernelEquiv.symm
              (ρ'.apply (a.quotientEquiv (X.rightHom e)) t))) =
        e * X.inl (Multiplicative.ofAdd (a.kernelEquiv.symm t)) * e⁻¹
    have hintertwines :=
      a.symm.intertwines (a.quotientEquiv (X.rightHom e)) t
    rw [show
      a.kernelEquiv.symm
          (ρ'.apply (a.quotientEquiv (X.rightHom e)) t) =
        ρ.apply (X.rightHom e) (a.kernelEquiv.symm t) by
          simpa [AdditiveAction.Equiv.symm] using hintertwines]
    exact X.conjugation_inl e (a.kernelEquiv.symm t)

/-- The transported kernel inclusion uses the inverse additive-kernel equivalence. -/
@[simp]
theorem transport_inl (X : ExtensionOverAction (E := E) ρ)
    (a : AdditiveAction.Equiv ρ ρ') (t : T') :
    (X.transport a).inl (Multiplicative.ofAdd t) =
      X.inl (Multiplicative.ofAdd (a.kernelEquiv.symm t)) :=
  rfl

/-- The transported quotient projection uses the forward quotient equivalence. -/
@[simp]
theorem transport_rightHom (X : ExtensionOverAction (E := E) ρ)
    (a : AdditiveAction.Equiv ρ ρ') (e : E) :
    (X.transport a).rightHom e = a.quotientEquiv (X.rightHom e) :=
  rfl

private theorem ext_of_groupExtension
    {X X' : ExtensionOverAction (E := E) ρ}
    (h : X.toGroupExtension = X'.toGroupExtension) :
    X = X' := by
  cases X
  cases X'
  cases h
  rfl

/-- Transporting an extension over an action along the identity action equivalence is the
identity. -/
@[simp]
theorem transport_refl (X : ExtensionOverAction (E := E) ρ) :
    X.transport (AdditiveAction.Equiv.refl ρ) = X := by
  apply ext_of_groupExtension
  exact GroupExtension.transportEndpoints_refl X.toGroupExtension

/-- Transport of extensions over actions respects composition of action equivalences. -/
theorem transport_trans (X : ExtensionOverAction (E := E) ρ)
    (a : AdditiveAction.Equiv ρ ρ') (a' : AdditiveAction.Equiv ρ' ρ'') :
    (X.transport a).transport a' = X.transport (a.trans a') := by
  apply ext_of_groupExtension
  exact GroupExtension.transportEndpoints_trans X.toGroupExtension
    (AddEquiv.toMultiplicative a.kernelEquiv) a.quotientEquiv
    (AddEquiv.toMultiplicative a'.kernelEquiv) a'.quotientEquiv

/-- Transporting an extension over an action forward and then backward recovers it. -/
@[simp]
theorem transport_symm (X : ExtensionOverAction (E := E) ρ)
    (a : AdditiveAction.Equiv ρ ρ') :
    (X.transport a).transport a.symm = X := by
  apply ext_of_groupExtension
  exact GroupExtension.transportEndpoints_symm X.toGroupExtension
    (AddEquiv.toMultiplicative a.kernelEquiv) a.quotientEquiv

/-- Transporting an extension over an action backward and then forward recovers it. -/
@[simp]
theorem symm_transport (X : ExtensionOverAction (E := E) ρ')
    (a : AdditiveAction.Equiv ρ ρ') :
    (X.transport a.symm).transport a = X := by
  apply ext_of_groupExtension
  exact GroupExtension.symm_transportEndpoints X.toGroupExtension
    (AddEquiv.toMultiplicative a.kernelEquiv) a.quotientEquiv

end ExtensionOverAction

end WallpaperGroups
