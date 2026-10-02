# Manual theorem audit log

This file records manual theorem-audit dispositions that should not change theorem-catalog review
signals. In particular, declarations with no current structural audit signal belong here rather than
in `theorem-catalog-retained.md`.

`theorem-catalog-retained.md` remains the active suppression list for declarations that currently
have a terminal, zero/single compiled-consumer, or direct-wrapper signal but are intentionally kept.
This log may also record private helpers, generated companions, and already-well-connected public API.

## Previously reviewed declarations moved out of the retained signal list

These declarations were reviewed in batches 05–07 and retained, but they do not currently have a
structural audit signal and therefore should not suppress any review queue.

- `Combinatorics.FamilySlotShuffleTo.blockInversionCount_of_ne` — retain public; explicit
  distinct-block expansion used by component crossing/parity proofs.
- `Finpartition.partGlobalSlot_injective` — retain public; structural injectivity of the
  part-to-ambient-slot map.
- `Finpartition.card_partGlobalSlots` — retain public; canonical cardinality of a part's ambient
  slot set.
- `Finpartition.partGlobalSlot_partOrderOfOrder` — retain public `[simp]`; canonical evaluation of
  the induced part order.
- `Combinatorics.FiniteIndex.blockCoordinate_lt` — retain public; reusable row-major range bound.
- `Combinatorics.FiniteIndex.blockEquiv_cast_mul_add` — retain public; forward computation rule for
  the fixed-width block equivalence.
- `familyGlobalSlot_injective` — retain private; shared by the local cardinality and subtype
  equivalence constructions.
- `card_familyGlobalSlots` — retain private; reused by the canonical fiber-order construction and
  uniqueness proof.
- `Combinatorics.FiniteIndex.blockEquiv_lt_iff` — retain public; lexicographic-order theorem for
  flattened block coordinates.
- `Combinatorics.FiniteIndex.blockEquiv_symm_lt_symm_iff_fst_lt_of_ne` — retain public; canonical
  distinct-block order specialization.
- `Combinatorics.FiniteIndex.blockEquiv_symm_lt_symm_iff_snd_lt_of_fst_eq` — retain public;
  canonical same-block order specialization.

## Batch 08

Reviewed the next ten previously unaudited catalog declarations after the audited fixed-width block
order results, skipping the already-retained
`Combinatorics.FiniteIndex.eq_cast_mul_add_blockEquiv`.

- `Combinatorics.FiniteIndex.card_deletedPositions` — retain public `[simp]`; canonical cardinality
  of the positions remaining after deleting the first slot and one distinct slot. It feeds the
  order-isomorphism definition and first-pair recursion proof.
- `Combinatorics.MultiplicativeWeight.cumulantFromMoment_objectMoment` — retain public; fundamental
  Möbius-inversion endpoint recovering the connected contribution from the raw object moment.
- `Combinatorics.MultiplicativeWeight.normalizedObjectMoment_apply` — retain public `[simp]`;
  canonical projection from the normalized wrapper to the raw object moment.
- `Combinatorics.MultiplicativeWeight.normalizedObjectMoment_cumulant_eq_connectedContribution` —
  retain public; domain-facing normalized cumulant endpoint used by bosonic, fermionic, and power
  series connected-contribution theorems.
- `Combinatorics.MultiplicativeWeight.objectMoment_eq_momentFromCumulant` — retain public; central
  forward connected-decomposition moment theorem, reused by inversion, replica, and permutation
  developments.
- `Combinatorics.MultiplicativeWeight.weight_decompose` — retain public; defining multiplicativity
  field/projection of `MultiplicativeWeight`, not a removable proof-routing wrapper.
- `Combinatorics.NormalizedSetFunction.cumulant_apply` — retain public `[simp]`; canonical
  evaluation rule for the bundled cumulant transform.
- `Combinatorics.NormalizedSetFunction.cumulant_moment` — retain public; one half of the
  moment–cumulant inverse laws and the left-inverse theorem used by `momentCumulantEquiv`.
- `Combinatorics.NormalizedSetFunction.ext` — retain public; canonical extensionality theorem for
  normalized finite-set functions.
- `Combinatorics.NormalizedSetFunction.ext_iff` — retain generated companion; produced by the
  extensionality machinery and already excluded from the manual extension-theorem review queue.

No declaration in batch 08 is deleted, inlined, privatized, or promoted.
