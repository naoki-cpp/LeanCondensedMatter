---
status: accepted
---

# Derive crystal structure from weak atomic configurations

Represent an atomic configuration only by its occupied sites and the species label on each site. Keep discreteness and periodicity as separate predicates; derive translations, lattices, motifs, and crystallographic groups from the geometry instead of storing them as redundant primitive data.

Define the full symmetry group using species-preserving ambient isometries, then derive the translation subgroup and its actions on sites. A periodic configuration has discrete translation vectors forming a full Mathlib `ℤ`-lattice and finitely many occupied-site orbits modulo translations. A finite motif and its site decomposition are existence results; the motif is not canonical stored data.

Use the full species-preserving symmetry group as the space-symmetry group. The pure translations form a normal subgroup, and the quotient is canonically equivalent to the image of the linear-part homomorphism (the point group). Do not assume this group extension splits: the representation must allow nonsymmorphic symmetries.

Reuse Mathlib's affine/isometry, group-action, subgroup/quotient, and lattice structures. Add project-specific abstractions only when they carry mathematical content beyond those canonical structures.

Evidence: [atomic configuration](../../LeanCondensedMatter/Crystal/AtomicConfiguration.lean), [symmetries](../../LeanCondensedMatter/Crystal/Symmetry.lean), [translations](../../LeanCondensedMatter/Crystal/Translation.lean), [periodicity and finite motifs](../../LeanCondensedMatter/Crystal/Periodicity.lean), [physical reciprocal lattice](../../LeanCondensedMatter/Crystal/Lattice.lean), [Brillouin quotient](../../LeanCondensedMatter/Crystal/Brillouin.lean), and [point group](../../LeanCondensedMatter/Crystal/PointGroup.lean).


## Historical evidence

[Issue #2838](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2838) proposes a finite one-dimensional Kronig–Penney benchmark connecting the existing Brillouin quotient to explicit Bloch-band formation. Reuse the crystal momentum and phase convention, while keeping the transfer matrix, discriminant, allowed-band/gap predicate, and band-edge assumptions model-local. The open issue adds no thermodynamic, transport, Berry, or topological result.

[Issue #1228](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1228) records the implemented weak-primitive, derived-periodicity, motif, and crystallographic quotient design. This ADR covers the implemented structural phases only; lattice-coordinate and low-dimensional classification work remains downstream in the still-open roadmap.

[Issue #2257](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2257) completes the derived finite-motif API with a unique translation–motif normal form when translations act freely on occupied sites. [Issue #2261](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2261) fixes the reusable theorem at the general `FiniteModuloTranslations` plus `IsCancelVAdd` boundary, so periodic torsor-valued configurations consume it without a model-specific forwarding theorem. The motif and representatives are chosen noncomputably by the theorem and remain derived results; do not store a unit cell, transversal, quotient, or motif as primitive `AtomicConfiguration` data. Current source: [periodicity and translation normal forms](../../LeanCondensedMatter/Crystal/Periodicity.lean).

[Issue #2232](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2232) extends that derived crystal boundary to reciprocal space. Represent a full Bravais lattice directly by Mathlib's `Submodule ℤ V` with `DiscreteTopology` and `IsZLattice ℝ`; do not add a competing `BravaisLattice` wrapper. Put the physical convention in one reciprocal pairing, `(2π)⁻¹⟨G,R⟩`, and define the reciprocal lattice through Mathlib's bilinear-form dual-submodule API. The Brillouin torus is only a thin `QuotientAddGroup` alias with a Bloch-phase periodicity bridge. Generic lattice and quotient structure remains in Mathlib; the physical reciprocal interpretation belongs in `Crystal`, not `Transport`. Current source: [reciprocal lattice](../../LeanCondensedMatter/Crystal/Lattice.lean) and [Brillouin quotient](../../LeanCondensedMatter/Crystal/Brillouin.lean). The issue remains open for downstream consumer integration; this records the landed substrate, not completed Brillouin-zone integration or TKNN.

[Issue #2266](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2266) derives the point group from the full species-preserving symmetry group by its linear-part homomorphism. Pure translations are exactly the kernel, and Mathlib's quotient-by-kernel/range equivalence identifies the point group; do not add a stored duplicate space group or assume the extension splits into a semidirect product. Current source: [point group and symmetry linear part](../../LeanCondensedMatter/Crystal/PointGroup.lean).

[Issue #2274](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2274) gives that point group its classification-facing action on the existing translation `ℤ`-lattice. Restrict each point-group isometry to a `ℤ`-linear automorphism; prove faithfulness only for full periodic lattices, and leave basis-dependent matrices or `GL(n, ℤ)` coordinates to a later consumer. Reuse the lattice submodule and Mathlib `LinearEquiv` rather than introducing a second lattice or matrix-group type. Current source: [point-group lattice representation](../../LeanCondensedMatter/Crystal/Classification.lean).
