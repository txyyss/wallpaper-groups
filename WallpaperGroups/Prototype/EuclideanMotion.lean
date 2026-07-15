import Mathlib.Analysis.Normed.Affine.Isometry

set_option linter.style.header false

/-!
# M0 Euclidean-motion prototype

This file is compiling evidence for the M0 representation decision.  Its declarations live in
`WallpaperGroups.Prototype`; the stable M1 API will be introduced separately.
-/

set_option autoImplicit false

namespace WallpaperGroups.Prototype

noncomputable section

/-- The M0 candidate for Euclidean motions of a real normed vector space. -/
abbrev EuclideanMotionCandidate (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  AffineIsometryEquiv ℝ E E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pure translation by `t`, using mathlib's affine-isometry constructor. -/
def translationCandidate (t : E) : EuclideanMotionCandidate E :=
  AffineIsometryEquiv.constVAdd ℝ E t

/-- The image of the origin, which is the translation component of an affine isometry. -/
def translationPartCandidate (g : EuclideanMotionCandidate E) : E :=
  g 0

/-- The linear-isometry component exposed by mathlib's affine-isometry API. -/
def linearPartCandidate (g : EuclideanMotionCandidate E) : E ≃ₗᵢ[ℝ] E :=
  g.linearIsometryEquiv

/-- An affine isometry acts as its linear part followed by addition of its translation part. -/
theorem apply_eq_translationPart_add (g : EuclideanMotionCandidate E) (x : E) :
    g x = translationPartCandidate g + linearPartCandidate g x := by
  change g x = g 0 + g.linearIsometryEquiv x
  calc
    g x = g (x +ᵥ (0 : E)) := by simp
    _ = g.linearIsometryEquiv x +ᵥ g 0 := g.map_vadd 0 x
    _ = g 0 + g.linearIsometryEquiv x := by
      change g.linearIsometryEquiv x + g 0 = g 0 + g.linearIsometryEquiv x
      exact add_comm _ _

/-- Translation components obey `(v, A) * (w, B) = (v + A w, A * B)`. -/
theorem translationPart_mul (g h : EuclideanMotionCandidate E) :
    translationPartCandidate (g * h) =
      translationPartCandidate g + linearPartCandidate g (translationPartCandidate h) := by
  change g (h 0) = g 0 + g.linearIsometryEquiv (h 0)
  calc
    g (h 0) = g (h 0 +ᵥ (0 : E)) := by simp
    _ = g.linearIsometryEquiv (h 0) +ᵥ g 0 := g.map_vadd 0 (h 0)
    _ = g 0 + g.linearIsometryEquiv (h 0) := by
      change g.linearIsometryEquiv (h 0) + g 0 = g 0 + g.linearIsometryEquiv (h 0)
      exact add_comm _ _

/-- Linear components multiply in the same order as affine isometries. -/
theorem linearPart_mul (g h : EuclideanMotionCandidate E) :
    linearPartCandidate (g * h) = linearPartCandidate g * linearPartCandidate h := by
  apply LinearIsometryEquiv.ext
  intro x
  rfl

/-- The inverse has translation component `-A⁻¹v`. -/
theorem translationPart_inv (g : EuclideanMotionCandidate E) :
    translationPartCandidate g⁻¹ =
      -(linearPartCandidate g)⁻¹ (translationPartCandidate g) := by
  change g.symm 0 = -g.linearIsometryEquiv.symm (g 0)
  apply g.injective
  rw [g.apply_symm_apply]
  conv_rhs =>
    rw [show -g.linearIsometryEquiv.symm (g 0) =
        -g.linearIsometryEquiv.symm (g 0) +ᵥ (0 : E) by simp]
  rw [g.map_vadd]
  simp

@[simp]
theorem translationPart_translation (t : E) :
    translationPartCandidate (translationCandidate t) = t := by
  simp [translationPartCandidate, translationCandidate]

@[simp]
theorem linearPart_translation (t : E) :
    linearPartCandidate (translationCandidate t) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  rfl

/-- Pure translations compose by addition. -/
theorem translation_add (t u : E) :
    translationCandidate (t + u) = translationCandidate t * translationCandidate u := by
  apply AffineIsometryEquiv.ext
  intro x
  simp only [translationCandidate, AffineIsometryEquiv.coe_constVAdd,
    AffineIsometryEquiv.coe_mul, Function.comp_apply]
  exact add_assoc t u x

/-- Conjugation sends translation by `t` to translation by the linear image of `t`. -/
theorem conjugate_translation (g : EuclideanMotionCandidate E) (t : E) :
    g * translationCandidate t * g⁻¹ =
      translationCandidate (linearPartCandidate g t) := by
  apply AffineIsometryEquiv.ext
  intro x
  change g (t + g.symm x) = g.linearIsometryEquiv t + x
  rw [show t + g.symm x = t +ᵥ g.symm x by rfl]
  rw [g.map_vadd, g.apply_symm_apply]
  rfl

end

end WallpaperGroups.Prototype
