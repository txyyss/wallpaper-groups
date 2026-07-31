# Lean declaration 初步双向索引

> 状态：第一阶段审计稿，等待审核；随正文逐章精化。
>
> 审计基线：`a2805a99348302d2dfae7c427a7bb890260ec665`

## 0. 索引约定

- 除非表中给出完整名称，declaration 均位于命名空间 `WallpaperGroups` 下。
- “陈述形状/边界”只作检索摘要；正文中的 `Lean statement` 将逐字核对完整量词、类型和假设。
- `Nonempty X` 或 `∃` 只表示存在，不能在讲义中改写成规范选择。
- 本索引采用拟议的新目录编号；目录尚待审核。

## 1. 讲义概念 → Lean declaration

### 第 01 章：平面等距变换、平移格与强平面群

| 讲义概念 | Declaration | Source file | 陈述形状/关键边界 |
|---|---|---|---|
| 欧氏平面 | `Plane` | `Basic/Plane.lean` | `EuclideanSpace ℝ (Fin 2)` |
| 欧氏运动 | `EuclideanMotion` | `Basic/EuclideanMotion.lean` | `AffineIsometryEquiv ℝ E E` |
| 线性部分、平移部分 | `EuclideanMotion.linearPart`, `EuclideanMotion.translationPart` | `Basic/EuclideanMotion.lean` | 每个 affine isometry 的线性与平移分量 |
| 平移 | `EuclideanMotion.translation` | `Basic/EuclideanMotion.lean` | 由向量构造欧氏运动 |
| 共轭平移公式 | `EuclideanMotion.conjugate_translation` | `Basic/EuclideanMotion.lean` | 线性部分作用于平移向量 |
| 秩二格 | `RankTwoLattice` | `Basic/RankTwoLattice.lean` | 整子模、选定 `Fin 2` 基及其实线性无关性 |
| 格坐标 | `RankTwoLattice.coordinates` | `Basic/RankTwoLattice.lean` | 依赖选定整基 |
| 换基 | `RankTwoLattice.reframe` | `Basic/RankTwoLattice.lean` | 同一载体配另一整基 |
| 换基矩阵共轭 | `RankTwoLattice.matrix_conjugacy_reframe` | `Basic/RankTwoLattice.lean` | 作用矩阵按 `GL₂(ℤ)` 共轭变化 |
| 格同构的实延拓 | `RankTwoLattice.extendEquiv` | `Basic/RankTwoLattice.lean` | 实线性同构，不保证等距 |
| 完整平移子群 | `EuclideanMotion.translationSubgroup` | `Invariants/Translation.lean` | 线性部分为一的群元素 |
| 平移向量 | `EuclideanMotion.translationVectors` | `Invariants/Translation.lean` | 从完整平移子群提取向量 |
| 点群 | `EuclideanMotion.pointGroup` | `Invariants/PointGroup.lean` | 线性部分的像 |
| 点群投影 | `EuclideanMotion.pointProjection` | `Invariants/PointGroup.lean` | 运动群到点群的满同态 |
| 点群在线性空间上的作用 | `EuclideanMotion.pointAction` | `Invariants/PointGroup.lean` | 点群元素作为线性等距变换 |
| 点群短正合列 | `EuclideanMotion.pointGroupExtension` | `Invariants/ExactSequence.lean` | `GroupExtension (translationSubgroup G) G (pointGroup G)` |
| 强平面群 | `PlaneGroup` | `Basic/PlaneGroup.lean` | 内置完整秩二平移格与有限点群 |
| 点群的格作用 | `PlaneGroup.latticeAction` | `Invariants/IntegralAction.lean` | 点群保持完整平移格 |
| 忠实整数表示 | `PlaneGroup.integralRepresentation`, `PlaneGroup.integralRepresentation_injective` | `Invariants/IntegralAction.lean` | \(H(G)\hookrightarrow GL_2(\mathbb Z)\) |
| 保持平移的抽象同构 | `TranslationPreservingIso` | `Basic/Equivalence.lean` | 群同构且完整平移子群的 map 恰等于目标平移子群 |
| V1 等价 | `PlaneGroup.Equivalent` | `Basic/Equivalence.lean` | `Nonempty (TranslationPreservingIso G H)` |
| 诱导点群同构 | `TranslationPreservingIso.pointGroupEquiv` | `Basic/Equivalence.lean` | 由商群自然诱导，不选择 lift |
| 格作用共轭 | `TranslationPreservingIso.latticeAction_conjugacy` | `Invariants/EquivalenceAction.lean` | 平移格同构 intertwine 点群作用 |
| 整数矩阵共轭 | `TranslationPreservingIso.integralRepresentation_conjugacy` | `Invariants/EquivalenceAction.lean` | 选定基下的 `GL₂(ℤ)` 共轭 |
| 换基不改变等价类 | `PlaneGroup.reframeIso`, `PlaneGroup.reframe_equivalent` | `Basic/Equivalence.lean` | framing 不是分类不变量 |

### 第 02 章：二维晶体学限制定理

| 讲义概念 | Declaration | Source file | 陈述形状/关键边界 |
|---|---|---|---|
| 方向保持点子群 | `orientationPreservingPointGroup` | `Restriction/Orientation.lean` | 点群中实行列式为正的子群 |
| 正号等距变换行列式为一 | `positive_isometry_det_eq_one` | `Restriction/Orientation.lean` | 二维线性等距变换的边界事实 |
| 复旋转参数 | `rotationParameter` | `Restriction/Orientation.lean` | \(H^+(G)\to\mathbb C^\times\) 的群同态 |
| 参数忠实性 | `rotationParameter_injective` | `Restriction/Orientation.lean` | 旋转参数单射 |
| 方向保持点子群循环 | `orientationPreserving_isCyclic` | `Restriction/Orientation.lean` | `IsCyclic (orientationPreservingPointGroup G)` |
| 反向元共轭到逆元 | `pointGroup_reversing_conjugates_to_inverse` | `Restriction/Orientation.lean` | \(srs^{-1}=r^{-1}\) |
| 反向点群元平方 | `pointGroup_reversing_sq` | `Restriction/Orientation.lean` | \(s^2=1\)，仅是点群元素 |
| 两个点群陪集 | `pointGroup_rotation_or_reflection_mul` | `Restriction/Orientation.lean` | 每个元素是 rotation 或 \(s\cdot\)rotation |
| 二面体结构数据 | `DihedralData` | `Restriction/Orientation.lean` | 循环 rotation 子群、反射元及两陪集分解 |
| cyclic/dihedral 析取 | `pointGroup_cyclic_or_dihedralData` | `Restriction/Orientation.lean` | `IsCyclic P ∨ Nonempty (DihedralData P)`；不保证互斥 |
| 五种允许阶 | `CrystallographicOrder` | `Restriction/Crystallographic.lean` | `one`, `two`, `three`, `four`, `six` |
| 阶数谓词 | `IsCrystallographicOrder` | `Restriction/Crystallographic.lean` | 存在上述枚举值，其 `toNat` 等于给定自然数 |
| 整数矩阵与环境矩阵一致 | `PlaneGroup.realMatrix_eq_ambientMatrix` | `Restriction/Crystallographic.lean` | 在格诱导的实基中比较 |
| 迹与行列式 cast | `PlaneGroup.trace_cast`, `PlaneGroup.det_cast` | `Restriction/Crystallographic.lean` | 整数表示与环境实线性变换的不变量相同 |
| 等距变换迹界 | `trace_bounds` | `Restriction/Crystallographic.lean` | 实迹位于 \([-2,2]\) |
| 迹为边界时的变换 | `eq_one_of_trace_eq_two`, `eq_neg_of_trace_eq_neg_two` | `Restriction/Crystallographic.lean` | 迹 \(2\) 得单位，迹 \(-2\) 得负单位 |
| 二维整数 Cayley–Hamilton | `cayley_hamilton` | `Restriction/Crystallographic.lean` | 对 \(2\times2\) 整数矩阵 |
| 三、四、六阶矩阵判据 | `order_three`, `order_four`, `order_six` | `Restriction/Crystallographic.lean` | 结合指定迹与行列式一得到精确阶 |
| 迹的五种整数值 | `PlaneGroup.integral_trace_cases` | `Restriction/Crystallographic.lean` | \(-2,-1,0,1,2\) |
| 正向作用行列式一 | `PlaneGroup.integral_det_eq_one` | `Restriction/Crystallographic.lean` | 需要正行列式假设 |
| 迹—精确阶表 | `PlaneGroup.orientationPreserving_trace_order_cases` | `Restriction/Crystallographic.lean` | \(-2,-1,0,1,2\leftrightarrow2,3,4,6,1\) 的分情况结论 |
| 元素级限制 | `PlaneGroup.orientationPreserving_order_isCrystallographic` | `Restriction/Crystallographic.lean` | 每个方向保持点群元素之阶为晶体学阶 |
| 元素级枚举 | `PlaneGroup.orientationPreserving_order_eq_toNat` | `Restriction/Crystallographic.lean` | `∃ q, orderOf h = q.toNat` |
| 子群级限制 | `PlaneGroup.orientationPreserving_subgroup_order_isCrystallographic` | `Restriction/Crystallographic.lean` | 方向保持子群的 `Nat.card` 为晶体学阶 |
| 子群级枚举 | `PlaneGroup.orientationPreserving_subgroup_order_eq_toNat` | `Restriction/Crystallographic.lean` | `∃ q, Nat.card H⁺ = q.toNat` |
| 秩二格中最短非零向量 | `RankTwoLattice.ShortestVector`, `RankTwoLattice.exists_shortestVector` | `Restriction/LatticeNormalForms.lean` | 存在性，不是规范选择 |
| 最短轨道向量线性无关 | `RankTwoLattice.shortest_orbit_real_linearIndependent` | `Restriction/LatticeNormalForms.lean` | 对迹参数 \(-1,0,1\) 的相应等距作用 |
| 最短轨道基 | `RankTwoLattice.shortestOrbitBasis` | `Restriction/LatticeNormalForms.lean` | 由 \(t,At\) 构造整数基 |
| 三种旋转矩阵 | `rotationMatrix3`, `rotationMatrix4`, `rotationMatrix6` | `Restriction/LatticeNormalForms.lean` | 列约定下分别为 `rotationMatrix (-1/0/1)` |
| 格作用正规形 bundle | `PlaneGroup.LatticeActionNormalForm` | `Restriction/LatticeNormalForms.lean` | 最短向量、orbit basis 及矩阵等式 |
| 迹参数正规形 | `PlaneGroup.exists_latticeActionNormalForm_of_trace` | `Restriction/LatticeNormalForms.lean` | 迹为 \(-1,0,1\) 时返回 `Nonempty` |
| 阶 \(3,4,6\) 正规形 | `PlaneGroup.exists_orderThree_latticeActionNormalForm`, `PlaneGroup.exists_orderFour_latticeActionNormalForm`, `PlaneGroup.exists_orderSix_latticeActionNormalForm` | `Restriction/LatticeNormalForms.lean` | 只声称存在相应 orbit basis |

### 第 03 章：无反射分类

| 讲义概念 | Declaration | Source file | 陈述形状/关键边界 |
|---|---|---|---|
| 无反射族 | `PointGroupHasNoReflections` | `Classification/NoReflections.lean` | 所有点群元素方向保持 |
| 无反射点群循环 | `pointGroup_isCyclic_of_noReflections` | `Classification/NoReflections.lean` | 由第 02 章循环性得到 |
| 点群阶为晶体学阶 | `noReflections_pointGroup_card_isCrystallographic` | `Classification/NoReflections.lean` | 点群基数属于 \(1,2,3,4,6\) |
| 无反射签名 | `noReflectionSignature` | `Classification/NoReflections.lean` | 非规范证明中提取唯一 `CrystallographicOrder`，值由点群阶确定 |
| 分裂循环扩张数据 | `splitCyclicPointExtensionOfNoReflections` | `Classification/NoReflections.lean` | 选择生成元和 lift；最终等价不依赖选择 |
| 同点群阶给出等价 | `equivalent_of_noReflections_of_pointGroup_card_eq` | `Classification/NoReflections.lean` | 还使用格作用正规形与扩张比较 |
| 签名完全性 | `equivalent_noReflections_iff_signature_eq` | `Classification/NoReflections.lean` | V1 等价当且仅当签名相等 |
| 五个旋转模型 | `rotationModel` | `Models/RotationModels.lean` | `CrystallographicOrder → PlaneGroup` |
| 模型签名 | `rotationModel_hasNoReflections`, `rotationModel_signature` | `Classification/NoReflections.lean` | 模型族与阶数计算 |
| 五类存在唯一性 | `classify_no_reflections` | `Classification/NoReflections.lean` | `∃! q, Equivalent G (rotationModel q)` |

### 第 04 章：单反射分类

| 讲义概念 | Declaration | Source file | 陈述形状/关键边界 |
|---|---|---|---|
| 单反射族 | `PointGroupHasOneReflection` | `Classification/OneReflection.lean` | 存在反向元，且所有正向元为一 |
| 单反射点群生成元 | `oneReflectionGenerator` | `Classification/OneReflection.lean` | 非规范选择 |
| 反射格类型 | `IntegralReflection.ReflectionLatticeKind` | `Restriction/ReflectionNormalForms.lean` | `primitive` 或 `centered` |
| 反射格正规形 | `PlaneGroup.ReflectionLatticeNormalForm` | `Restriction/ReflectionNormalForms.lean` | 选定 basis 下的整矩阵正规形 |
| 正规形存在 | `PlaneGroup.exists_reflectionLatticeNormalForm` | `Restriction/ReflectionNormalForms.lean` | 返回非规范正规形 |
| 有限 norm | `finiteNormHom` | `Invariants/ShiftClass.lean` | \(N_h(t)=\sum_{i=0}^{q-1}h^i t\) |
| 固定子群与 norm 子群 | `fixedTranslationSubgroup`, `normTranslationSubgroup` | `Invariants/ShiftClass.lean` | shift quotient 的分子与分母 |
| shift 商群 | `ShiftClassGroup` | `Invariants/ShiftClass.lean` | \(T^h/N_h(T)\) |
| lift 的周期幂向量 | `liftPowerTranslation` | `Invariants/ShiftClass.lean` | 依赖 lift 的原始向量 |
| shift class | `shiftClass` | `Invariants/ShiftClass.lean` | 原始向量在商群中的类 |
| lift 独立性 | `shiftClass_lift_independent` | `Invariants/ShiftClass.lean` | 两个 lift 的商类相同 |
| 等价下的 shift transport | `shiftClassEquiv`, `shiftClass_natural` | `Invariants/ShiftClass.lean` | 输入 `TranslationPreservingIso`，并 transport 相应点群元素与周期 |
| 反射扩张数据 | `ReflectionExtensionData` | `Presentations/ReflectionExtension.lean` | 含选定 lift 及其平方 shift |
| 调整 lift | `ReflectionExtensionData.adjust` | `Presentations/ReflectionExtension.lean` | raw shift 增加 norm |
| 商类相等时的扩张同构 | `reflectionExtensionIsoOfShiftDifference` | `Presentations/ReflectionExtension.lean` | 从 norm 差见证调整 lift |
| 三个标签 | `OneReflectionType` | `Classification/OneReflection.lean` | `cm`, `pm`, `pg` |
| 三类存在性 | `equivalent_cm_of_centered`, `equivalent_pm_of_primitive_norm`, `equivalent_pg_of_primitive_nonNorm` | `Classification/OneReflection.lean` | centered；primitive+zero shift；primitive+nonzero shift |
| 模型唯一性 | `oneReflectionModels_equivalent_iff` | `Classification/OneReflection.lean` | 两模型等价当且仅当标签相等 |
| 三类分类 | `classify_one_reflection` | `Classification/OneReflection.lean` | `∃! w : OneReflectionType, Equivalent G w.model` |

### 第 05 章：多反射分类与十七类定理

| 讲义概念 | Declaration | Source file | 陈述形状/关键边界 |
|---|---|---|---|
| 多反射族 | `PointGroupHasMultipleReflections` | `Invariants/ReflectionFamilies.lean` | 有反向元且有非平凡正向元 |
| 三族析取 | `pointGroup_reflection_trichotomy` | `Invariants/ReflectionFamilies.lean` | 无反射、单反射、多反射三种情形 |
| 二面体生成数据 | `DihedralGenerators` | `Restriction/DihedralNormalForms.lean` | 旋转生成元、第一反射及关系 |
| 生成数据存在 | `exists_dihedralGenerators` | `Restriction/DihedralNormalForms.lean` | 多反射假设下存在，选择不规范 |
| 六种联合格作用类型 | `DihedralLatticeForm` | `Restriction/DihedralNormalForms.lean` | 按旋转阶与反射格作用区分 |
| 联合格正规形 | `PlaneGroup.DihedralLatticeNormalForm` | `Restriction/DihedralNormalForms.lean` | 同一 basis 同时正规化旋转和反射 |
| 联合正规形存在 | `PlaneGroup.exists_dihedralLatticeNormalForm` | `Restriction/DihedralNormalForms.lean` | `Nonempty`；basis 非规范 |
| 双反射扩张数据 | `TwoReflectionExtensionData` | `Presentations/TwoReflectionExtension.lean` | 两个相邻反射 lift 及 shift |
| 两个 shift class | `TwoReflectionExtensionData.firstShiftClass`, `TwoReflectionExtensionData.secondShiftClass` | `Presentations/TwoReflectionExtension.lean` | 各自取相应 norm 商类 |
| 调整两个 lift | `TwoReflectionExtensionData.adjust` | `Presentations/TwoReflectionExtension.lean` | 两个 raw shift 分别增加 norm |
| 精确数据的扩张同构 | `TwoReflectionExtensionData.twoReflectionExtensionIsoExact` | `Presentations/TwoReflectionExtension.lean` | 调整后 raw presentation 数据精确匹配 |
| 商类数据的扩张同构 | `TwoReflectionExtensionData.twoReflectionExtensionIsoOfShiftClasses` | `Presentations/TwoReflectionExtension.lean` | 从两个 shift class 相等提取调整量 |
| 有限陪集模型数据 | `FiniteCosetData` | `Models/DihedralModels.lean` | 含非规范 section/shift 数据 |
| 由有限陪集构造强平面群 | `finiteCosetPlaneGroup` | `Models/DihedralModels.lean` | 显式模型构造 |
| 九个标签 | `MultipleReflectionType` | `Models/DihedralModels.lean` | `cmm,pmm,pmg,pgg,p3m1,p31m,p4m,p4g,p6m` |
| 模型扩张数据 | `multipleReflectionModelData` | `Models/DihedralModels.lean` | 每个模型的显式有限陪集数据 |
| 多反射模型存在性 | `exists_equivalent_multipleReflectionModel` | `Classification/ManyReflections.lean` | 任意多反射群等价于某个九类模型 |
| 消失反射类计数 | `vanishingReversingPointCount` | `Invariants/ReflectionShiftCount.lean` | shift class 为零的反向点群元素数 |
| 计数的等价不变性 | `TranslationPreservingIso.vanishingReversingPointCount_eq` | `Invariants/ReflectionShiftCount.lean` | V1 等价下保持 |
| centered 全体反向作用 | `PlaneGroup.AllReversingActionsCentered` | `Classification/MultipleReflectionInequivalence.lean` | 分离 `cmm` 与 `pmm` |
| 反射轴生成子模 | `PlaneGroup.reflectionAxisSpan` | `Restriction/DihedralNormalForms.lean` | 分离两种三阶联合格作用 |
| `p3m1/p31m` 不等价 | `PlaneGroup.DihedralLatticeNormalForm.p3m1_not_equivalent_p31m` | `Restriction/DihedralNormalForms.lean` | 一个轴子模为顶，另一个商为 `ZMod 3` |
| 九模型唯一性 | `MultipleReflectionType.models_equivalent_iff` | `Classification/MultipleReflectionInequivalence.lean` | 模型等价当且仅当标签相等 |
| 九类分类 | `classify_multiple_reflections` | `Classification/MultipleReflectionInequivalence.lean` | `∃! w : MultipleReflectionType, Equivalent G w.model` |
| 十七个标签 | `WallpaperType` | `Models/WallpaperModels.lean` | 精确枚举 5+3+9 |
| 分类签名 | `WallpaperSignature`, `wallpaperSignatureEquiv` | `Models/WallpaperModels.lean` | 按三族包装标签 |
| 十七模型唯一性 | `WallpaperType.models_equivalent_iff` | `Classification/Wallpaper.lean` | 模型等价当且仅当标签相等 |
| 模型存在性 | `exists_equivalent_wallpaperModel` | `Classification/Wallpaper.lean` | 每个强平面群等价于某个模型 |
| 十七类总分类 | `classification` | `Classification/Wallpaper.lean` | `∀ G, ∃! w, Equivalent G w.model`；额外假设已编码在 `G` 中 |
| 等价类商 | `PlaneGroup.EquivalenceClass` | `Classification/PlaneGroupClasses.lean` | `Quotient PlaneGroup.equivalentSetoid` |
| 标签与等价类双射 | `WallpaperType.equivalenceClassEquiv` | `Classification/PlaneGroupClasses.lean` | `WallpaperType ≃ PlaneGroup.EquivalenceClass` |
| 等价类数为 17 | `PlaneGroup.equivalenceClass_card_eq_seventeen` | `Classification/PlaneGroupClasses.lean` | `Nat.card ... = 17` |

### 第 06 章：运动类型、几何定义与强定义桥接

| 讲义概念 | Declaration | Source file | 陈述形状/关键边界 |
|---|---|---|---|
| 运动的行列式 | `PlaneMotion.determinant` | `Geometry/MotionType.lean` | affine 运动线性部分的实行列式 |
| 有不动点 | `PlaneMotion.HasFixedPoint` | `Geometry/MotionType.lean` | 存在 \(x\) 使 \(g x=x\) |
| 平移 | `PlaneMotion.IsTranslation` | `Geometry/MotionType.lean` | 线性部分为一；包含恒等元 |
| 旋转 | `PlaneMotion.IsRotation` | `Geometry/MotionType.lean` | 行列式正且不是平移 |
| 反射 | `PlaneMotion.IsReflection` | `Geometry/MotionType.lean` | 行列式负且有不动点 |
| 滑移反射 | `PlaneMotion.IsGlideReflection` | `Geometry/MotionType.lean` | 行列式负且无不动点 |
| 反射的代数判据 | `PlaneMotion.isReflection_iff` | `Geometry/MotionType.lean` | 行列式负且 \(g^2=1\) |
| 滑移反射的代数判据 | `PlaneMotion.isGlideReflection_iff` | `Geometry/MotionType.lean` | 行列式负且 \(g^2\ne1\) |
| 四类运动保持同构 | `MotionTypePreservingIso` | `Geometry/MotionType.lean` | 抽象群同构加四个 iff 字段 |
| 强群 textbook 等价 | `PlaneGroup.TextbookEquivalent` | `Geometry/MotionType.lean` | `Nonempty MotionTypePreservingIso` |
| 与 V1 等价一致 | `PlaneGroup.textbookEquivalent_iff_equivalent` | `Geometry/MotionType.lean` | 两个抽象关系逻辑等价 |
| 强群 textbook 分类 | `textbook_classification` | `Geometry/MotionType.lean` | 恰有一个 `WallpaperType` |
| 作用意义的离散性 | `MotionSubgroup.IsDiscrete` | `Geometry/GeometricWallpaperGroup.lean` | `ProperlyDiscontinuousSMul Γ Plane` |
| 余紧性 | `MotionSubgroup.IsCocompact` | `Geometry/GeometricWallpaperGroup.lean` | 存在紧集，其群平移覆盖平面 |
| 几何墙纸群 | `GeometricWallpaperGroup` | `Geometry/GeometricWallpaperGroup.lean` | 只有 carrier、离散性、余紧性 |
| 强定义推出离散 | `PlaneGroup.motionGroup_isDiscrete` | `Geometry/StrongToGeometric.lean` | 使用完整秩二平移格与有限点群 |
| 强定义推出余紧 | `PlaneGroup.motionGroup_isCocompact` | `Geometry/StrongToGeometric.lean` | 使用格平行四边形紧基本域 |
| 强到几何 | `PlaneGroup.toGeometricWallpaperGroup` | `Geometry/StrongToGeometric.lean` | carrier 不变 |
| 恢复完整平移格 | `GeometricWallpaperGroup.translationLattice` | `Geometry/TranslationLatticeRecovery.lean` | basis 由存在性选择；载体是完整平移模块 |
| 几何到强 | `GeometricWallpaperGroup.toPlaneGroup` | `Geometry/GeometricClassification.lean` | carrier 不变 |
| 同 carrier 的强结构等价 | `PlaneGroup.equivalent_of_carrier_eq` | `Geometry/GeometricClassification.lean` | 消除 basis/proof-field 选择 |
| 强—几何—强往返 | `PlaneGroup.toGeometric_toPlaneGroup` | `Geometry/GeometricClassification.lean` | 只声称 `Equivalent`，不声称 record 相等 |
| 恢复选择独立 | `GeometricWallpaperGroup.toPlaneGroup_choice_independent` | `Geometry/GeometricClassification.lean` | 任一同 carrier 强包装都与恢复者等价 |
| 几何运动类型同构 | `GeometricWallpaperGroup.MotionTypePreservingIso` | `Geometry/GeometricClassification.lean` | 几何 carrier 间的四类保持抽象同构 |
| 几何 textbook 等价 | `GeometricWallpaperGroup.TextbookEquivalent` | `Geometry/GeometricClassification.lean` | `Nonempty` 上述同构 |
| 几何/强 textbook 对照 | `GeometricWallpaperGroup.textbookEquivalent_iff_toPlaneGroup` | `Geometry/GeometricClassification.lean` | 转成强群后比较 |
| 几何/V1 等价对照 | `GeometricWallpaperGroup.textbookEquivalent_iff_equivalent` | `Geometry/GeometricClassification.lean` | 右侧是恢复强群的 V1 等价 |
| 十七类几何分类 | `geometric_classification` | `Geometry/GeometricClassification.lean` | 每个几何墙纸群 textbook-equivalent 于唯一几何模型 |

### 第 07 章：群扩张、截面与二余循环

| 讲义概念 | Declaration | Source file | 陈述形状/关键边界 |
|---|---|---|---|
| 加法群作用 | `AdditiveAction` | `Extensions/Action.lean` | `H →* Multiplicative (AddAut T)` |
| 固定作用的扩张 | `ExtensionOverAction` | `Extensions/Action.lean` | `GroupExtension` 加上共轭作用与给定 \(\rho\) 一致 |
| 规范二余循环 | `NormalizedCocycle` | `Extensions/NormalizedCocycle.lean` | 规范化条件与 cocycle 恒等式 |
| 规范一余链 | `NormalizedCochain` | `Extensions/NormalizedCocycle.lean` | \(b(1)=0\) |
| coboundary | `NormalizedCochain.coboundary` | `Extensions/NormalizedCocycle.lean` | \(\delta b(g,h)=b(g)+\rho(g)b(h)-b(gh)\) |
| 改变二余循环 | `NormalizedCocycle.changeBy` | `Extensions/NormalizedCocycle.lean` | \(c\mapsto c+\delta b\) |
| 显式同调关系 | `CocycleCohomologous` | `Extensions/NormalizedCocycle.lean` | 存在规范一余链使 `d = c.changeBy b` |
| 同调关系 setoid | `CocycleCohomologous.setoid` | `Extensions/NormalizedCocycle.lean` | 源码没有另命名的 `H²` quotient |
| twisted product | `TwistedProduct` | `Extensions/TwistedProduct.lean` | \((t,g)(u,h)=(t+\rho(g)u+c(g,h),gh)\) |
| twisted-product 扩张 | `TwistedProduct.toExtensionOverAction` | `Extensions/TwistedProduct.lean` | 由 cocycle 构造固定作用扩张 |
| coboundary 坐标变换 | `TwistedProduct.changeByMulEquiv` | `Extensions/TwistedProduct.lean` | \((t,g)\mapsto(t-b(g),g)\) |
| 规范截面 | `NormalizedSection` | `Extensions/Section.lean` | `GroupExtension.Section` 且单位元规范化 |
| section factor | `NormalizedSection.factor` | `Extensions/Section.lean` | 非可计算选取，但由 `inl_factor` 唯一刻画 |
| 从 section 得 cocycle | `NormalizedSection.toCocycle` | `Extensions/Section.lean` | associativity 给出 cocycle identity |
| 两 section 的差 | `NormalizedSection.differenceCochain` | `Extensions/Section.lean` | kernel-valued 规范一余链 |
| 换 section 改变 coboundary | `NormalizedSection.toCocycle_change` | `Extensions/Section.lean` | 提取的 cocycle 相差显式 coboundary |
| 固定端点 twisted product 分类 | `TwistedProduct.extensionEquiv_iff_cocycleCohomologous` | `Extensions/Classification.lean` | 同 kernel、quotient、action |
| 固定作用的一般扩张分类 | `ExtensionOverAction.extensionEquiv_iff_cocycleCohomologous` | `Extensions/Classification.lean` | 需给两边规范截面 |
| 作用等价 | `AdditiveAction.Equiv` | `Extensions/Transport.lean` | 显式 kernel/quotient 等价及 intertwining |
| 异端点扩张等价 | `ExtensionOverAction.EquivAlong` | `Extensions/HeterogeneousClassification.lean` | 沿给定 action equivalence 比较 |
| 异端点分类 | `ExtensionOverAction.equivAlong_iff_cocycleCohomologous` | `Extensions/HeterogeneousClassification.lean` | transport 后 cocycle 同调当且仅当存在 `EquivAlong` |
| 点群向量扩张 | `EuclideanMotion.pointGroupVectorExtension` | `Extensions/PointGroup.lean` | 现有二维/欧氏运动适配器 |
| 点群固定作用扩张 | `EuclideanMotion.pointGroupExtensionOverAction` | `Extensions/PointGroup.lean` | 把点群扩张包装为 `ExtensionOverAction` |
| 二面体规范截面 | `dihedralNormalizedSection` | `Extensions/DihedralFactor.lean` | 适配 V1 的二面体 section |
| 二面体规范 cocycle | `dihedralNormalizedCocycle` | `Extensions/DihedralFactor.lean` | 现有 `dihedralFactor` 的 generic 包装 |

## 2. 当前没有对应 declaration 的延期项

| 规划中的联系 | 当前状态 | 讲义处理 |
|---|---|---|
| 任意 `TranslationPreservingIso` 到 M9 action/extension transport 的统一 adapter | 延期 | 只能解释预期关系 |
| 一般 `ShiftClass` 到 generic cyclic cocycle class | 延期 | 不写成定理 |
| 一般 `FiniteCosetData` 到 generic classifier | 延期 | 只介绍现有模型数据与 generic 理论的概念对应 |
| 任意秩 \(n\) 晶体扩张专门化 | 延期 | 不属于本讲义已证明成果 |
| 与抽象 \(H^2\) 的比较 | 延期 | 使用“显式二余循环商关系”，不声称已构造标准 \(H^2\) |

## 3. 源码文件 → 讲义章节

这是反向索引的第一版；正文完成后将细化到小节与定理编号。

| Source file | 主要目标章节 |
|---|---|
| `Basic/Plane.lean` | 01 |
| `Basic/EuclideanMotion.lean` | 01 |
| `Basic/RankTwoLattice.lean` | 01 |
| `Basic/PlaneGroup.lean` | 01、06 |
| `Basic/Equivalence.lean` | 01、03、04、05、06 |
| `Invariants/Translation.lean` | 01 |
| `Invariants/PointGroup.lean` | 01 |
| `Invariants/ExactSequence.lean` | 01、03、04、05、07 |
| `Invariants/IntegralAction.lean` | 01、02 |
| `Invariants/EquivalenceAction.lean` | 01、02、03、04、05 |
| `Restriction/Orientation.lean` | 02 |
| `Restriction/Crystallographic.lean` | 02 |
| `Restriction/LatticeNormalForms.lean` | 02、03 |
| `Presentations/CyclicExtension.lean` | 03 |
| `Models/RotationModels.lean` | 03 |
| `Classification/NoReflections.lean` | 03 |
| `Invariants/ShiftClass.lean` | 04、05 |
| `Restriction/ReflectionNormalForms.lean` | 04 |
| `Presentations/ReflectionExtension.lean` | 04 |
| `Models/ReflectionModels.lean` | 04 |
| `Classification/OneReflection.lean` | 04 |
| `Invariants/ReflectionFamilies.lean` | 03、04、05 |
| `Restriction/DihedralNormalForms.lean` | 05 |
| `Presentations/DihedralExtension.lean` | 05、07 |
| `Presentations/TwoReflectionExtension.lean` | 05 |
| `Models/DihedralModels.lean` | 05 |
| `Invariants/ReflectionShiftCount.lean` | 05 |
| `Classification/ManyReflections.lean` | 05 |
| `Classification/MultipleReflectionInequivalence.lean` | 05 |
| `Models/WallpaperModels.lean` | 05 |
| `Classification/Wallpaper.lean` | 05 |
| `Classification/PlaneGroupClasses.lean` | 05 |
| `Geometry/MotionType.lean` | 06 |
| `Geometry/GeometricWallpaperGroup.lean` | 06 |
| `Geometry/StrongToGeometric.lean` | 06 |
| `Geometry/GeometricToStrong.lean` | 06 |
| `Geometry/TranslationLatticeRecovery.lean` | 06 |
| `Geometry/GeometricClassification.lean` | 06 |
| `Extensions/Action.lean` | 07 |
| `Extensions/NormalizedCocycle.lean` | 07 |
| `Extensions/TwistedProduct.lean` | 07 |
| `Extensions/Section.lean` | 07 |
| `Extensions/Classification.lean` | 07 |
| `Extensions/Transport.lean` | 07 |
| `Extensions/EndpointTransport.lean` | 07 |
| `Extensions/HeterogeneousClassification.lean` | 07 |
| `Extensions/PointGroup.lean` | 01、07 |
| `Extensions/DihedralFactor.lean` | 05、07 |
