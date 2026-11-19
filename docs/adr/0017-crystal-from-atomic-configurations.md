---
status: accepted
---

# Derive crystal structure from weak atomic configurations

Represent an atomic configuration only by its occupied sites and the species label on each site. Keep discreteness and periodicity as separate predicates; derive translations, lattices, motifs, and crystallographic groups from the geometry instead of storing them as redundant primitive data.

Define the full symmetry group using species-preserving ambient isometries, then derive the translation subgroup and its actions on sites. A periodic configuration has discrete translation vectors forming a full Mathlib `ℤ`-lattice and finitely many occupied-site orbits modulo translations. A finite motif and its site decomposition are existence results; the motif is not canonical stored data.

Use the full species-preserving symmetry group as the space-symmetry group. The pure translations form a normal subgroup, and the quotient is canonically equivalent to the image of the linear-part homomorphism (the point group). Do not assume this group extension splits: the representation must allow nonsymmorphic symmetries.

Use the reciprocal pairing `(2π)⁻¹⟨G,R⟩` and Brillouin quotient for the physical Bloch-phase convention. Reuse Mathlib's affine/isometry, group-action, subgroup/quotient, and lattice structures. Add project-specific abstractions only when they carry mathematical content beyond those canonical structures.

Lattice geometry and atomic-configuration classification have separate owners.
[Gram matrices and lattice automorphisms](../../LeanCondensedMatter/Crystal/LatticePointGroup/Gram.lean),
[planar basis reduction](../../LeanCondensedMatter/Crystal/LatticePointGroup/PlanarReduction.lean), and
[planar Gram constraints](../../LeanCondensedMatter/Crystal/LatticePointGroup/PlanarGram.lean)
describe the lattice itself. [Classification](../../LeanCondensedMatter/Crystal/Classification.lean)
owns the configuration point group's integral representation and crystallographic restriction.
Import the owner needed by a consumer; the `Crystal` umbrella groups these related APIs.

Evidence: [atomic configuration](../../LeanCondensedMatter/Crystal/AtomicConfiguration.lean), [symmetries](../../LeanCondensedMatter/Crystal/Symmetry.lean), [translations](../../LeanCondensedMatter/Crystal/Translation.lean), [periodicity and finite motifs](../../LeanCondensedMatter/Crystal/Periodicity.lean), [physical reciprocal lattice](../../LeanCondensedMatter/Crystal/Lattice.lean), [Brillouin quotient](../../LeanCondensedMatter/Crystal/Brillouin.lean), and [point group](../../LeanCondensedMatter/Crystal/PointGroup.lean).
