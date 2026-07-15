Review status: approved

# M3 specification review

This packet records the implemented meaning of “two-dimensional crystallographic restriction”
and the lattice normal forms that M4–M6 will consume.  It requests approval; it is not approval.

## Orientation-preserving subgroup

`WallpaperGroups/Restriction/Orientation.lean` defines

```lean
def orientationPreservingPointGroup (G : PlaneGroup) :
    Subgroup (EuclideanMotion.pointGroup G.carrier) where
  carrier := {h | 0 < ((pointGroupDet G h : ℝˣ) : ℝ)}
  ...
```

Thus membership means that the determinant of the underlying real-linear isometry is positive.
For a plane isometry this determinant is then proved to be exactly `1`; it is not an extra field
or hypothesis on `PlaneGroup`.

## Crystallographic orders and main restriction theorem

`WallpaperGroups/Restriction/Crystallographic.lean` exports

```lean
inductive CrystallographicOrder
  | one | two | three | four | six
  deriving DecidableEq, Fintype

def CrystallographicOrder.toNat : CrystallographicOrder → ℕ

def IsCrystallographicOrder (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6
```

The theorem about the order of the whole positive subgroup is

```lean
theorem PlaneGroup.orientationPreserving_subgroup_order_isCrystallographic
    (G : PlaneGroup) :
    IsCrystallographicOrder
      (Nat.card (orientationPreservingPointGroup G))
```

The elementwise theorem used to prove it and by later generator arguments is

```lean
theorem PlaneGroup.orientationPreserving_order_isCrystallographic
    (G : PlaneGroup) (h : orientationPreservingPointGroup G) :
    IsCrystallographicOrder (orderOf h.1)
```

Typed existential forms are also exported as
`orientationPreserving_subgroup_order_eq_toNat` and
`orientationPreserving_order_eq_toNat`.

### Complete assumptions

The subgroup-order theorem assumes only `G : PlaneGroup`.  It uses exactly the M2 fields already
stored in that structure:

- the full translation carrier as a framed rank-two integer lattice;
- equality of that carrier with all translation vectors of `G.carrier`;
- finiteness of `EuclideanMotion.pointGroup G.carrier`.

The elementwise theorem additionally takes
`h : orientationPreservingPointGroup G`, whose only extra fact is positive determinant by the
definition above.  No discreteness, cocompactness, primitive-vector, chosen-angle, faithful-action,
or splitting assumption has been added.  Faithfulness of the integral action and full real span
are reused M2 theorems.

## Cyclicity, reversing conjugation, and dihedral form

The exact cyclicity theorem is

```lean
theorem orientationPreserving_isCyclic (G : PlaneGroup) :
    IsCyclic (orientationPreservingPointGroup G)
```

It is proved by the injective homomorphism `rotationParameter` into `ℂ`.  For every reversing
element and every positive element, the exported conjugation theorem is

```lean
lemma pointGroup_reversing_conjugates_to_inverse
    (G : PlaneGroup) (s : EuclideanMotion.pointGroup G.carrier)
    (hs : s ∉ orientationPreservingPointGroup G)
    (r : orientationPreservingPointGroup G) :
    s * r.1 * s⁻¹ = (r.1)⁻¹
```

In particular, `exists_orientationGenerator` chooses a cyclic generator and states that every
reversing element conjugates that generator to its inverse.  Reversing elements also satisfy
`pointGroup_reversing_sq : s ^ 2 = 1`.

The cyclic/dihedral conclusion is

```lean
theorem pointGroup_cyclic_or_dihedralData (G : PlaneGroup) :
    IsCyclic (EuclideanMotion.pointGroup G.carrier) ∨
      Nonempty (DihedralData (EuclideanMotion.pointGroup G.carrier))
```

`DihedralData` contains the cyclic positive subgroup, a reversing involution, inversion by
conjugation, and the normal form saying every point-group element is either a rotation or the
selected reversing element times a rotation.  This covers an all-positive cyclic group, a trivial
rotation subgroup with one reversing involution, and every nontrivial dihedral case.

## Lattice-basis normal forms for orders 3, 4, and 6

`WallpaperGroups/Restriction/LatticeNormalForms.lean` defines

```lean
def rotationMatrix (c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, c]
def rotationMatrix3 : Matrix (Fin 2) (Fin 2) ℤ := rotationMatrix (-1)
def rotationMatrix4 : Matrix (Fin 2) (Fin 2) ℤ := rotationMatrix 0
def rotationMatrix6 : Matrix (Fin 2) (Fin 2) ℤ := rotationMatrix 1
```

The result bundle

```lean
structure PlaneGroup.LatticeActionNormalForm
    (G : PlaneGroup) (h : EuclideanMotion.pointGroup G.carrier)
    (M : Matrix (Fin 2) (Fin 2) ℤ) where
  shortest : G.translationLattice.ShortestVector
  basis : Module.Basis (Fin 2) ℤ G.translationLattice.carrier
  basis_zero : basis 0 = shortest.vector
  basis_one : basis 1 = G.latticeAction h shortest.vector
  matrix_eq :
    LinearMap.toMatrix basis basis (G.latticeAction h).toLinearMap = M
```

is produced by these three theorems:

```lean
theorem PlaneGroup.exists_orderThree_latticeActionNormalForm
    (G : PlaneGroup) (h : orientationPreservingPointGroup G)
    (horder : orderOf h.1 = 3) :
    Nonempty (LatticeActionNormalForm G h.1 rotationMatrix3)

theorem PlaneGroup.exists_orderFour_latticeActionNormalForm
    (G : PlaneGroup) (h : orientationPreservingPointGroup G)
    (horder : orderOf h.1 = 4) :
    Nonempty (LatticeActionNormalForm G h.1 rotationMatrix4)

theorem PlaneGroup.exists_orderSix_latticeActionNormalForm
    (G : PlaneGroup) (h : orientationPreservingPointGroup G)
    (horder : orderOf h.1 = 6) :
    Nonempty (LatticeActionNormalForm G h.1 rotationMatrix6)
```

Consequently the selected `t` is shortest and nonzero, is primitive because it is the first
element of an integer basis, and `(t, h t)` is the full translation-lattice basis.  The precise
matrix, not merely an unspecified integral conjugacy, is available directly to M4–M6.

## Proof route and alternatives

The formal order-restriction proof follows Roadmap route A:

1. identify the real cast of `latticeActionMatrix` with the ambient isometry matrix;
2. prove the real trace lies in `[-2, 2]` and the integral determinant is `1`;
3. enumerate the five integer traces;
4. apply the two-dimensional Cayley–Hamilton identity to obtain exact orders
   `2, 3, 4, 6, 1` for traces `-2, -1, 0, 1, 2`;
5. combine elementwise restriction with cyclicity to identify the subgroup cardinality.

A shortest-vector proof is used only to construct the separately required lattice bases.  The
carrier is the integer span of the derived real basis, so bounded intersections are finite and a
shortest nonzero vector exists.  Centering real orbit coordinates with `round` gives a remainder
whose squared norm is at most `3/4 * ‖t‖²`; minimality forces it to be zero.

The full shortest-vector/angle proof of the order restriction was abandoned because it would
duplicate the trace proof and add angle case analysis.  Integral-conjugacy classification inside
`SL₂(ℤ)` was also abandoned because it needs arithmetic normal-form machinery and does not by
itself produce the required shortest orbit vector.  Only the route described above remains in
production.  FD-011 records this choice and is awaiting the same human approval as M3.

## Differences from the paper and Roadmap

- There is no substantive change to the allowed orders or to the strength of the orbit-basis
  result.
- The paper's informal “cyclic or dihedral” conclusion is represented by project-local
  `DihedralData`, rather than immediately choosing an isomorphism to a convention-dependent
  `DihedralGroup n`.  It explicitly records precisely the generator, conjugation, and two-coset
  facts required later, including the order-two boundary case.
- The standard matrices follow mathlib's column-vector convention fixed by FD-010.  Their columns
  express `t ↦ h t` and the Cayley–Hamilton relation for `h (h t)`.
- Unlike the paper, existence of a shortest vector is not assumed from discreteness: discreteness
  and finiteness of bounded lattice intersections are derived from the stored rank-two basis.

## Files and declarations requiring owner attention

- `WallpaperGroups/Restriction/Orientation.lean`:
  `orientationPreservingPointGroup`, `orientationPreserving_isCyclic`,
  `pointGroup_reversing_conjugates_to_inverse`, `DihedralData`, and
  `pointGroup_cyclic_or_dihedralData`.
- `WallpaperGroups/Restriction/Crystallographic.lean`:
  `CrystallographicOrder`, `IsCrystallographicOrder`,
  `PlaneGroup.orientationPreserving_subgroup_order_isCrystallographic`, and
  `PlaneGroup.orientationPreserving_trace_order_cases`.
- `WallpaperGroups/Restriction/LatticeNormalForms.lean`:
  `RankTwoLattice.ShortestVector`, `RankTwoLattice.shortestOrbitBasis`,
  `PlaneGroup.LatticeActionNormalForm`, and the three order-specific existence theorems.
- `docs/FOUNDATION_DECISIONS.md`: FD-011.

The owner should focus on whether positive determinant is the intended subgroup definition;
whether `DihedralData` has all required boundary cases; and whether carrying a shortest vector,
the full orbit basis, and an exact standard matrix is sufficient for M4–M6.

## Verification recorded for this review

- each of the three new production Lean modules compiles independently with no diagnostics;
- `lake build` completes successfully (`2840` jobs);
- `git diff --check` succeeds;
- the `*.lean` project-source scan finds no `sorry`, `admit`, new `axiom`, or `unsafe`;
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are unchanged from `m2-complete`.
