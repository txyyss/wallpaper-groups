import WallpaperGroups.Classification.MultipleReflectionInequivalence
import WallpaperGroups.Classification.NoReflections
import WallpaperGroups.Classification.OneReflection

set_option linter.style.header false

/-!
# The seventeen standard wallpaper models

This file is the common model index for the final classification.  It does not construct new
geometric subgroups: it packages the five rotation models, three one-reflection models, and nine
multiple-reflection models already proved correct in M4--M6.
-/

set_option autoImplicit false

namespace WallpaperGroups

noncomputable section

open PlaneGroup
open EuclideanMotion

/-- The seventeen wallpaper-group labels.  The paper's `p4mm`, `p4mg`, and `p6mm` are exported
under their modern short names `p4m`, `p4g`, and `p6m`. -/
inductive WallpaperType
  | p1 | p2 | p3 | p4 | p6
  | cm | pm | pg
  | cmm | pmm | pmg | pgg | p3m1 | p31m | p4m | p4g | p6m
  deriving DecidableEq, Fintype

/-- The standard plane group attached to a wallpaper label. -/
def WallpaperType.model : WallpaperType → PlaneGroup
  | .p1 => p1Model
  | .p2 => p2Model
  | .p3 => p3Model
  | .p4 => p4Model
  | .p6 => p6Model
  | .cm => cmModel
  | .pm => pmModel
  | .pg => pgModel
  | .cmm => cmmModel
  | .pmm => pmmModel
  | .pmg => pmgModel
  | .pgg => pggModel
  | .p3m1 => p3m1Model
  | .p31m => p31mModel
  | .p4m => p4mModel
  | .p4g => p4gModel
  | .p6m => p6mModel

/-- The proved `5 + 3 + 9` decomposition of the label set. -/
inductive WallpaperSignature
  | noReflections (order : CrystallographicOrder)
  | oneReflection (type : OneReflectionType)
  | multipleReflections (type : MultipleReflectionType)
  deriving DecidableEq, Fintype

/-- Forget the printed label while retaining its component-classification signature. -/
def WallpaperType.signature : WallpaperType → WallpaperSignature
  | .p1 => .noReflections .one
  | .p2 => .noReflections .two
  | .p3 => .noReflections .three
  | .p4 => .noReflections .four
  | .p6 => .noReflections .six
  | .cm => .oneReflection .cm
  | .pm => .oneReflection .pm
  | .pg => .oneReflection .pg
  | .cmm => .multipleReflections .cmm
  | .pmm => .multipleReflections .pmm
  | .pmg => .multipleReflections .pmg
  | .pgg => .multipleReflections .pgg
  | .p3m1 => .multipleReflections .p3m1
  | .p31m => .multipleReflections .p31m
  | .p4m => .multipleReflections .p4m
  | .p4g => .multipleReflections .p4g
  | .p6m => .multipleReflections .p6m

/-- Recover the printed wallpaper label from its component signature. -/
def WallpaperSignature.wallpaperType : WallpaperSignature → WallpaperType
  | .noReflections .one => .p1
  | .noReflections .two => .p2
  | .noReflections .three => .p3
  | .noReflections .four => .p4
  | .noReflections .six => .p6
  | .oneReflection .cm => .cm
  | .oneReflection .pm => .pm
  | .oneReflection .pg => .pg
  | .multipleReflections .cmm => .cmm
  | .multipleReflections .pmm => .pmm
  | .multipleReflections .pmg => .pmg
  | .multipleReflections .pgg => .pgg
  | .multipleReflections .p3m1 => .p3m1
  | .multipleReflections .p31m => .p31m
  | .multipleReflections .p4m => .p4m
  | .multipleReflections .p4g => .p4g
  | .multipleReflections .p6m => .p6m

@[simp]
theorem WallpaperSignature.signature_wallpaperType (s : WallpaperSignature) :
    s.wallpaperType.signature = s := by
  cases s with
  | noReflections q => cases q <;> rfl
  | oneReflection w => cases w <;> rfl
  | multipleReflections w => cases w <;> rfl

@[simp]
theorem WallpaperType.wallpaperType_signature (w : WallpaperType) :
    w.signature.wallpaperType = w := by
  cases w <;> rfl

/-- The label set is canonically the disjoint sum of the three component signatures. -/
def wallpaperSignatureEquiv : WallpaperType ≃ WallpaperSignature where
  toFun := WallpaperType.signature
  invFun := WallpaperSignature.wallpaperType
  left_inv := WallpaperType.wallpaperType_signature
  right_inv := WallpaperSignature.signature_wallpaperType

/-- The standard model attached directly to a component signature. -/
def WallpaperSignature.model : WallpaperSignature → PlaneGroup
  | .noReflections q => rotationModel q
  | .oneReflection w => w.model
  | .multipleReflections w => w.model

@[simp]
theorem WallpaperType.signature_model (w : WallpaperType) :
    w.signature.model = w.model := by
  cases w <;> rfl

/-- The full point-group order of a standard wallpaper model. -/
def WallpaperType.pointGroupOrder : WallpaperType → ℕ
  | .p1 => 1
  | .p2 | .cm | .pm | .pg => 2
  | .p3 => 3
  | .p4 | .cmm | .pmm | .pmg | .pgg => 4
  | .p6 => 6
  | .p3m1 | .p31m => 6
  | .p4m | .p4g => 8
  | .p6m => 12

/-- Every one of the seventeen models has the advertised finite point group. -/
@[simp]
theorem WallpaperType.model_pointGroup_card (w : WallpaperType) :
    Nat.card (pointGroup w.model.carrier) = w.pointGroupOrder := by
  cases w <;> simp [WallpaperType.model, WallpaperType.pointGroupOrder]

/-- The explicit lattice used by a standard wallpaper model. -/
def WallpaperType.lattice : WallpaperType → RankTwoLattice Plane
  | .cm | .cmm => centeredLattice
  | .p3 | .p6 | .p3m1 | .p31m | .p6m => hexLattice
  | _ => RankTwoLattice.standardLattice

/-- Every standard model's full translation subgroup is exactly its advertised lattice. -/
@[simp]
theorem WallpaperType.model_translationLattice (w : WallpaperType) :
    w.model.translationLattice = w.lattice := by
  cases w <;> rfl

/-- The predicate appropriate to the component containing a signature. -/
def WallpaperSignature.FamilyPredicate (s : WallpaperSignature) : Prop :=
  match s with
  | .noReflections _ => PointGroupHasNoReflections s.model
  | .oneReflection _ => PointGroupHasOneReflection s.model
  | .multipleReflections _ => PointGroupHasMultipleReflections s.model

/-- Every component model lies in its advertised reflection family. -/
theorem WallpaperSignature.model_family (s : WallpaperSignature) : s.FamilyPredicate := by
  cases s with
  | noReflections q => exact rotationModel_hasNoReflections q
  | oneReflection w => exact oneReflectionModel_hasOneReflection w
  | multipleReflections w => exact multipleReflectionModel_hasMultipleReflections w

end

end WallpaperGroups
