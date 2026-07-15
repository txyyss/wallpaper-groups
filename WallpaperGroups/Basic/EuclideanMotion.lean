import Mathlib.Analysis.Normed.Affine.Isometry

set_option linter.style.header false

/-!
# Euclidean motions

This module gives a thin project interface to mathlib's affine isometric equivalences.  A motion
is kept coordinate-free; its translation part is its value at the origin and its linear part is
the canonical linear isometry supplied by mathlib.
-/

set_option autoImplicit false

namespace WallpaperGroups

/-- The group of Euclidean motions of a real normed vector space. -/
abbrev EuclideanMotion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  AffineIsometryEquiv ℝ E E

namespace EuclideanMotion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The translation component of a Euclidean motion, obtained by evaluating it at the origin. -/
def translationPart (g : EuclideanMotion E) : E :=
  g 0

/-- The linear-isometry component of a Euclidean motion, as a group homomorphism. -/
def linearPart : EuclideanMotion E →* (E ≃ₗᵢ[ℝ] E) where
  toFun g := g.linearIsometryEquiv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    rfl
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    rfl

/-- A linear isometry regarded as a Euclidean motion fixing the origin. -/
def pureLinear : (E ≃ₗᵢ[ℝ] E) →* EuclideanMotion E where
  toFun A := A.toAffineIsometryEquiv
  map_one' := by
    apply AffineIsometryEquiv.ext
    intro x
    rfl
  map_mul' A B := by
    apply AffineIsometryEquiv.ext
    intro x
    rfl

/-- The pure translation by a vector `t`. -/
def translation (t : E) : EuclideanMotion E :=
  AffineIsometryEquiv.constVAdd ℝ E t

/-- A pure translation acts by adding its translation vector. -/
@[simp]
theorem translation_apply (t x : E) : translation t x = t + x :=
  rfl

/-- A pure linear motion acts by its underlying linear isometry. -/
@[simp]
theorem pureLinear_apply (A : E ≃ₗᵢ[ℝ] E) (x : E) : pureLinear A x = A x :=
  rfl

/-- The identity motion has zero translation part. -/
@[simp]
theorem translationPart_one : translationPart (1 : EuclideanMotion E) = 0 :=
  rfl

/-- The bundled linear-part homomorphism agrees with mathlib's canonical field. -/
@[simp]
theorem linearPart_apply (g : EuclideanMotion E) : linearPart g = g.linearIsometryEquiv :=
  rfl

/-- The identity motion has identity linear part. -/
@[simp]
theorem linearPart_one : linearPart (1 : EuclideanMotion E) = 1 :=
  map_one linearPart

/-- Linear parts preserve multiplication of motions. -/
@[simp]
theorem linearPart_mul (g h : EuclideanMotion E) :
    linearPart (g * h) = linearPart g * linearPart h :=
  map_mul linearPart g h

/-- Linear parts preserve inverses of motions. -/
@[simp]
theorem linearPart_inv (g : EuclideanMotion E) :
    linearPart g⁻¹ = (linearPart g)⁻¹ :=
  map_inv linearPart g

/-- The translation part of pure translation by `t` is `t`. -/
@[simp]
theorem translationPart_translation (t : E) : translationPart (translation t) = t := by
  simp [translationPart, translation]

/-- A pure translation has trivial linear part. -/
@[simp]
theorem linearPart_translation (t : E) : linearPart (translation t) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  rfl

/-- A pure linear motion has zero translation part. -/
@[simp]
theorem translationPart_pureLinear (A : E ≃ₗᵢ[ℝ] E) : translationPart (pureLinear A) = 0 := by
  change A 0 = 0
  simp

/-- The linear part of a pure linear motion is the original linear isometry. -/
@[simp]
theorem linearPart_pureLinear (A : E ≃ₗᵢ[ℝ] E) : linearPart (pureLinear A) = A := by
  rfl

/-- A Euclidean motion acts as its linear part followed by addition of its translation part. -/
theorem apply_eq_translationPart_add (g : EuclideanMotion E) (x : E) :
    g x = translationPart g + linearPart g x := by
  change g x = g 0 + g.linearIsometryEquiv x
  calc
    g x = g (x +ᵥ (0 : E)) := by simp
    _ = g.linearIsometryEquiv x +ᵥ g 0 := g.map_vadd 0 x
    _ = g 0 + g.linearIsometryEquiv x := by
      change g.linearIsometryEquiv x + g 0 = g 0 + g.linearIsometryEquiv x
      exact add_comm _ _

/-- Translation components obey `(v, A) * (w, B) = (v + A w, A * B)`. -/
theorem translationPart_mul (g h : EuclideanMotion E) :
    translationPart (g * h) = translationPart g + linearPart g (translationPart h) := by
  change g (h 0) = g 0 + g.linearIsometryEquiv (h 0)
  calc
    g (h 0) = g (h 0 +ᵥ (0 : E)) := by simp
    _ = g.linearIsometryEquiv (h 0) +ᵥ g 0 := g.map_vadd 0 (h 0)
    _ = g 0 + g.linearIsometryEquiv (h 0) := by
      change g.linearIsometryEquiv (h 0) + g 0 = g 0 + g.linearIsometryEquiv (h 0)
      exact add_comm _ _

/-- The inverse has translation component `-A⁻¹v`. -/
theorem translationPart_inv (g : EuclideanMotion E) :
    translationPart g⁻¹ = -(linearPart g)⁻¹ (translationPart g) := by
  change g.symm 0 = -g.linearIsometryEquiv.symm (g 0)
  apply g.injective
  rw [g.apply_symm_apply]
  conv_rhs =>
    rw [show -g.linearIsometryEquiv.symm (g 0) =
        -g.linearIsometryEquiv.symm (g 0) +ᵥ (0 : E) by simp]
  rw [g.map_vadd]
  simp

/-- Translation by zero is the identity motion. -/
@[simp]
theorem translation_zero : translation (0 : E) = 1 := by
  apply AffineIsometryEquiv.ext
  intro x
  simp

/-- Pure translations compose according to vector addition. -/
theorem translation_add (t u : E) : translation (t + u) = translation t * translation u := by
  apply AffineIsometryEquiv.ext
  intro x
  simp only [translation_apply, AffineIsometryEquiv.coe_mul, Function.comp_apply]
  exact add_assoc t u x

/-- Negating a vector gives the inverse pure translation. -/
@[simp]
theorem translation_neg (t : E) : translation (-t) = (translation t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← translation_add]
  simp

/-- Pure translations, bundled as a homomorphism from the multiplicative tag of `E`. -/
def translationHom : Multiplicative E →* EuclideanMotion E where
  toFun t := translation t.toAdd
  map_one' := translation_zero
  map_mul' t u := by
    change translation (t.toAdd + u.toAdd) = translation t.toAdd * translation u.toAdd
    exact translation_add _ _

/-- Evaluating the bundled translation homomorphism recovers `translation`. -/
@[simp]
theorem translationHom_apply (t : Multiplicative E) : translationHom t = translation t.toAdd :=
  rfl

/-- Pure translation is injective. -/
theorem translation_injective : Function.Injective (translation : E → EuclideanMotion E) := by
  intro t u h
  simpa using congrArg translationPart h

/-- Two pure translations are equal exactly when their vectors are equal. -/
@[simp]
theorem translation_eq_iff {t u : E} : translation t = translation u ↔ t = u :=
  translation_injective.eq_iff

/-- Translation and linear parts determine a Euclidean motion. -/
theorem ext_parts {g h : EuclideanMotion E}
    (htranslation : translationPart g = translationPart h)
    (hlinear : linearPart g = linearPart h) : g = h := by
  apply AffineIsometryEquiv.ext
  intro x
  rw [apply_eq_translationPart_add, apply_eq_translationPart_add, htranslation, hlinear]

/-- Equality of motions is equivalent to equality of both components. -/
theorem ext_parts_iff {g h : EuclideanMotion E} :
    g = h ↔ translationPart g = translationPart h ∧ linearPart g = linearPart h := by
  constructor
  · intro hgh
    subst hgh
    exact ⟨rfl, rfl⟩
  · rintro ⟨ht, hl⟩
    exact ext_parts ht hl

/-- Every Euclidean motion is the product of its translation and linear components. -/
theorem translation_mul_pureLinear (g : EuclideanMotion E) :
    translation (translationPart g) * pureLinear (linearPart g) = g := by
  apply AffineIsometryEquiv.ext
  intro x
  rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, translation_apply, pureLinear_apply]
  exact (apply_eq_translationPart_add g x).symm

/-- A Euclidean motion with trivial linear part is its pure translation component. -/
theorem eq_translation_of_linearPart_eq_one {g : EuclideanMotion E} (hg : linearPart g = 1) :
    g = translation (translationPart g) := by
  apply ext_parts
  · simp
  · rw [linearPart_translation]
    exact hg

/-- Conjugation sends translation by `t` to translation by the linear image of `t`. -/
theorem conjugate_translation (g : EuclideanMotion E) (t : E) :
    g * translation t * g⁻¹ = translation (linearPart g t) := by
  apply AffineIsometryEquiv.ext
  intro x
  change g (t + g.symm x) = g.linearIsometryEquiv t + x
  rw [show t + g.symm x = t +ᵥ g.symm x by rfl]
  rw [g.map_vadd, g.apply_symm_apply]
  rfl

end

end EuclideanMotion

end WallpaperGroups
