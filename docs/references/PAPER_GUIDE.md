# Guide to Schwarzenberger, “The 17 plane symmetry groups”

## Bibliographic role

This paper is the project’s main elementary proof guide. It is not the formal specification and should not be translated line by line.

## Relevant pages

The PDF contains material from adjacent journal articles. The relevant article runs from printed page 123 through printed page 130.

- **Printed pp. 123–124:** Euclidean motions `(v, φ)`, the multiplication law, translation lattice `T`, point group `H`, action of `H` on `T`, and shift vectors.
- **Printed pp. 125–126:** the strong definition of a plane group, existence of a shortest lattice vector, cyclic rotation subgroup, crystallographic restriction, and the three reflection-shift situations.
- **Printed p. 127:** equivalence by an abstract group isomorphism mapping `T` onto `T'`; start of classification.
- **Printed pp. 127–128:** five reflection-free classes and three single-reflection classes.
- **Printed pp. 129–130:** nine multiple-reflection classes and the summary table.

## Formalization translation

Paper concept → project concept:

- pair `(v, φ)` → Euclidean motion / semidirect product element;
- lattice `T` → translation vectors with a rank-two `ℤ`-basis;
- point group `H` → image of the linear-part homomorphism;
- action of `H` on `T` → conjugation action on translations;
- shift vector → a quotient class in `T^h / N_h(T)`;
- equivalence → `TranslationPreservingIso`;
- the three large classification cases → M4, M5, and M6.

## Notation normalization

The project uses modern short names:

- paper `p4mm` → project `p4m`;
- paper `p4mg` → project `p4g`;
- paper `p6mm` → project `p6m`.

Keep `p3m1` and `p31m` distinct. Verify their assignment using explicit standard models and the page-130 table image rather than OCR alone.

## Warnings

- OCR in the PDF is unreliable for Greek letters, fractions, superscripts, and table entries.
- The proof suppresses some well-definedness and homomorphism calculations.
- The paper’s “shift vectors” are choice-dependent representatives; the formal invariant should be a quotient class.
- The paper assumes rank-two translations and finite point group. It does not establish this from discreteness and cocompactness.
- The classification equivalence is not Euclidean conjugacy.
