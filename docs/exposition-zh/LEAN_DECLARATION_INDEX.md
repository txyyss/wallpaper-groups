# 中文讲义 Lean declaration 双向索引

> 状态：第一版索引，基于 `main@2cba9284f7226649a77a6b12b6b042ad89d3541d`
> （Lean `4.33.0`，mathlib `v4.33.0`）。
>
> 本索引只列讲义主线所需的公开声明。私有证明引理和纯计算细节仍以源码为准。

## 1. 第 01 章：平面等距变换、平移格与强平面群

### 欧氏运动分解

源文件：`WallpaperGroups/Basic/EuclideanMotion.lean`

- `EuclideanMotion.translationPart`
- `EuclideanMotion.linearPart`
- `EuclideanMotion.translation`
- `EuclideanMotion.apply_eq_translationPart_add`
- `EuclideanMotion.translationPart_mul`
- `EuclideanMotion.linearPart_mul`
- `EuclideanMotion.translationPart_inv`
- `EuclideanMotion.eq_translation_of_linearPart_eq_one`
- `EuclideanMotion.conjugate_translation`

### 平移子群、点群与短正合列

源文件：

- `WallpaperGroups/Invariants/Translation.lean`
- `WallpaperGroups/Invariants/PointGroup.lean`
- `WallpaperGroups/Invariants/ExactSequence.lean`

关键声明：

- `EuclideanMotion.translationVectors`
- `EuclideanMotion.translationSubgroup`
- `EuclideanMotion.translationEquiv`
- `EuclideanMotion.pointGroup`
- `EuclideanMotion.pointProjection`
- `EuclideanMotion.pointProjection_ker`
- `EuclideanMotion.pointAction`
- `EuclideanMotion.pointActionHom`
- `EuclideanMotion.pointGroupExtension`
- `EuclideanMotion.pointGroupExtension_conjAct_translationSubgroupElement`

### 强 `PlaneGroup`、格作用与 V1 等价

源文件：

- `WallpaperGroups/Basic/PlaneGroup.lean`
- `WallpaperGroups/Basic/Equivalence.lean`
- `WallpaperGroups/Invariants/IntegralAction.lean`
- `WallpaperGroups/Invariants/EquivalenceAction.lean`

关键声明：

- `PlaneGroup`
- `TranslationPreservingIso`
- `PlaneGroup.Equivalent`
- `TranslationPreservingIso.translationVectorEquiv`
- `TranslationPreservingIso.translationLatticeEquiv`
- `TranslationPreservingIso.pointGroupEquiv`
- `TranslationPreservingIso.realLinearEquiv`
- `PlaneGroup.latticeAction`
- `PlaneGroup.latticeActionHom_injective`
- `PlaneGroup.integralRepresentation`
- `PlaneGroup.integralRepresentation_injective`
- `TranslationPreservingIso.integralRepresentation_conjugacy`
- `PlaneGroup.reframe_equivalent`

## 2. 第 02 章：二维晶体学限制定理

源文件：

- `WallpaperGroups/Restriction/Orientation.lean`
- `WallpaperGroups/Restriction/Crystallographic.lean`
- `WallpaperGroups/Restriction/LatticeNormalForms.lean`

### 点群结构

- `orientationPreservingPointGroup`
- `orientationPreserving_isCyclic`
- `pointGroup_reversing_conjugates_to_inverse`
- `pointGroup_reversing_sq`
- `DihedralData`
- `pointGroup_cyclic_or_dihedralData`

### 晶体学阶数限制

- `CrystallographicOrder`
- `IsCrystallographicOrder`
- `PlaneGroup.orientationPreserving_order_isCrystallographic`
- `PlaneGroup.orientationPreserving_subgroup_order_isCrystallographic`
- `PlaneGroup.orientationPreserving_trace_order_cases`

### 最短向量与格作用正规形

- `RankTwoLattice.ShortestVector`
- `RankTwoLattice.shortestOrbitBasis`
- `PlaneGroup.LatticeActionNormalForm`
- `rotationMatrix3`
- `rotationMatrix4`
- `rotationMatrix6`
- `PlaneGroup.exists_orderThree_latticeActionNormalForm`
- `PlaneGroup.exists_orderFour_latticeActionNormalForm`
- `PlaneGroup.exists_orderSix_latticeActionNormalForm`

## 3. 第 03 章：无反射五类

源文件：

- `WallpaperGroups/Presentations/CyclicExtension.lean`
- `WallpaperGroups/Models/RotationModels.lean`
- `WallpaperGroups/Classification/NoReflections.lean`

关键声明：

- `PointGroupHasNoReflections`
- `cyclicSplitting`
- `splitExtensionMulEquiv`
- `splitPlaneGroupIso`
- `cyclicExtensionIso`
- `rotationModel`
- `classify_no_reflections`

## 4. 第 04 章：单反射三类

源文件：

- `WallpaperGroups/Restriction/ReflectionNormalForms.lean`
- `WallpaperGroups/Invariants/ShiftClass.lean`
- `WallpaperGroups/Presentations/ReflectionExtension.lean`
- `WallpaperGroups/Models/ReflectionModels.lean`
- `WallpaperGroups/Classification/OneReflection.lean`

关键声明：

- `PointGroupHasOneReflection`
- `OneReflectionType`
- `ShiftClassGroup`
- `finiteNormHom`
- `shiftClass`
- `shiftClass_lift_independent`
- `shiftClass_natural`
- `ReflectionExtensionData`
- `ReflectionExtensionData.adjust`
- `reflectionExtensionIsoOfShiftDifference`
- `classify_one_reflection`

## 5. 第 05 章：多反射九类与十七类定理

源文件：

- `WallpaperGroups/Restriction/DihedralNormalForms.lean`
- `WallpaperGroups/Invariants/DihedralShift.lean`
- `WallpaperGroups/Presentations/DihedralExtension.lean`
- `WallpaperGroups/Presentations/TwoReflectionExtension.lean`
- `WallpaperGroups/Models/DihedralModels.lean`
- `WallpaperGroups/Classification/ManyReflections.lean`
- `WallpaperGroups/Classification/MultipleReflectionInequivalence.lean`
- `WallpaperGroups/Classification/Wallpaper.lean`
- `WallpaperGroups/Classification/PlaneGroupClasses.lean`

关键声明：

- `PointGroupHasMultipleReflections`
- `MultipleReflectionType`
- `DihedralExtensionData`
- `TwoReflectionExtensionData`
- `dihedralFactor`
- `twoReflectionExtensionIsoOfShiftClasses`
- `FiniteCosetData`
- `classify_multiple_reflections`
- `WallpaperType`
- `WallpaperType.model`
- `WallpaperType.models_equivalent_iff`
- `classification`
- `WallpaperType.equivalenceClassEquiv`
- `PlaneGroup.equivalenceClass_card_eq_seventeen`

## 6. 第 06 章：运动类型与几何桥接

### 四类运动与 textbook 等价

源文件：`WallpaperGroups/Geometry/MotionType.lean`

- `PlaneMotion.IsTranslation`
- `PlaneMotion.IsRotation`
- `PlaneMotion.IsReflection`
- `PlaneMotion.IsGlideReflection`
- `PlaneMotion.decomposition`
- `MotionTypePreservingIso`
- `PlaneGroup.TextbookEquivalent`
- `PlaneGroup.textbookEquivalent_iff_equivalent`
- `textbook_classification`

### 几何定义与强定义双向转换

源文件：

- `WallpaperGroups/Geometry/GeometricWallpaperGroup.lean`
- `WallpaperGroups/Geometry/StrongToGeometric.lean`
- `WallpaperGroups/Geometry/GeometricToStrong.lean`
- `WallpaperGroups/Geometry/TranslationLatticeRecovery.lean`
- `WallpaperGroups/Geometry/GeometricClassification.lean`

关键声明：

- `MotionSubgroup.IsDiscrete`
- `MotionSubgroup.IsCocompact`
- `GeometricWallpaperGroup`
- `MotionSubgroup.isCocompact_iff_compact_orbitSpace`
- `PlaneGroup.motionGroup_isDiscrete`
- `PlaneGroup.motionGroup_isCocompact`
- `PlaneGroup.toGeometricWallpaperGroup`
- `MotionSubgroup.pointGroup_finite`
- `MotionSubgroup.translationModule_discreteTopology`
- `MotionSubgroup.translationModule_span_eq_top`
- `GeometricWallpaperGroup.translationLattice`
- `GeometricWallpaperGroup.toPlaneGroup`
- `GeometricWallpaperGroup.toPlaneGroup_choice_independent`
- `PlaneGroup.toGeometric_toPlaneGroup`
- `GeometricWallpaperGroup.toPlaneGroup_toGeometric`
- `GeometricWallpaperGroup.TextbookEquivalent`
- `GeometricWallpaperGroup.textbookEquivalent_iff_equivalent`
- `geometric_classification`
- `GeometricWallpaperGroup.equivalenceClass_card_eq_seventeen`

## 7. 第 07 章后编：显式扩张理论

### 显式作用、二阶余循环与扭曲积

源文件：

- `WallpaperGroups/Extensions/Action.lean`
- `WallpaperGroups/Extensions/NormalizedCocycle.lean`
- `WallpaperGroups/Extensions/TwistedProduct.lean`
- `WallpaperGroups/Extensions/Section.lean`

关键声明：

- `AdditiveAction`
- `ExtensionOverAction`
- `NormalizedCocycle`
- `NormalizedCochain`
- `NormalizedCochain.coboundary`
- `CocycleCohomologous`
- `TwistedProduct`
- `TwistedProduct.toGroupExtension`
- `TwistedProduct.toExtensionOverAction`
- `TwistedProduct.changeByMulEquiv`
- `NormalizedSection`
- `NormalizedSection.factor`
- `NormalizedSection.toCocycle`
- `NormalizedSection.toCocycle_change`
- `TwistedProduct.canonicalSection_toCocycle`

### 固定作用与异构端点分类

源文件：

- `WallpaperGroups/Extensions/Classification.lean`
- `WallpaperGroups/Extensions/Transport.lean`
- `WallpaperGroups/Extensions/EndpointTransport.lean`
- `WallpaperGroups/Extensions/HeterogeneousClassification.lean`

关键声明：

- `TwistedProduct.changeByExtensionEquiv`
- `NormalizedSection.twistedProductExtensionEquiv`
- `TwistedProduct.extensionEquiv_iff_cocycleCohomologous`
- `ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous`
- `AdditiveAction.Equiv`
- `NormalizedCochain.transport`
- `NormalizedCocycle.transport`
- `CocycleCohomologous.transport_iff`
- `GroupExtension.relabelQuotient`
- `GroupExtension.transportEndpoints`
- `ExtensionOverAction.transport`
- `ExtensionOverAction.EquivAlong`
- `ExtensionOverAction.equivAlong_iff_cocycleCohomologous`

### 已实现的二维薄适配器

源文件：

- `WallpaperGroups/Extensions/PointGroup.lean`
- `WallpaperGroups/Extensions/DihedralFactor.lean`

- `EuclideanMotion.pointGroupVectorExtension`
- `EuclideanMotion.pointGroupExtensionOverAction`
- `dihedralNormalizedSection`
- `dihedralNormalizedCocycle`
- `dihedralFactor_cocycle`

## 8. 已延期、不得误写成现有 theorem 的适配器

- `TranslationPreservingIso` 到 M9 action/extension transport 的一般适配器；
- M5 `ShiftClass` 与 generic cyclic cocycle class 的比较；
- `FiniteCosetData` 与 generic cocycle classifier 的一般适配；
- 自由阿贝尔秩 `n` 的专门化接口；
- 与抽象 `H²` 的比较。

## 9. 源文件到讲义章节的反向索引

| 源码目录 | 讲义位置 |
|---|---|
| `Basic/`、`Invariants/Translation.lean`、`Invariants/PointGroup.lean`、`Invariants/ExactSequence.lean` | 第 01 章 |
| `Restriction/Orientation.lean`、`Restriction/Crystallographic.lean`、`Restriction/LatticeNormalForms.lean` | 第 02 章 |
| `Presentations/CyclicExtension.lean`、`Models/RotationModels.lean`、`Classification/NoReflections.lean` | 第 03 章 |
| `Restriction/ReflectionNormalForms.lean`、`Invariants/ShiftClass.lean`、`Presentations/ReflectionExtension.lean`、`Classification/OneReflection.lean` | 第 04 章 |
| `Restriction/DihedralNormalForms.lean`、`Invariants/DihedralShift.lean`、`Presentations/DihedralExtension.lean`、`Presentations/TwoReflectionExtension.lean`、`Classification/MultipleReflectionInequivalence.lean` | 第 05 章 |
| `Geometry/` | 第 06 章 |
| `Extensions/` | 第 07 章后编 |
