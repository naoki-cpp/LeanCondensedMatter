import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.VacuumLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairing
import LeanCondensedMatter.Combinatorics.InvolutionCard

set_option linter.style.header false

/-!
# The external component's positions in mixed-time order

The amplitude evaluates `pairingInMixedOrder`, which lives on positions ordered by interaction time,
not on the combinatorial leg indexing. Splitting the amplitude therefore has to happen there.

The payoff is that a subset of a linear order can be enumerated monotonically, so the induced
splitting satisfies the strict-monotonicity hypotheses of the crossing-sign factorization for free.
Those hypotheses are not a technical convenience: a pair value here is the expectation of an
*ordered* composition of operators, so a part only carries the same quantity the ambient does when
its embedding preserves order.

This module names the set of mixed-order positions lying in the external component, and records the
two facts a splitting needs: it is closed under the pairing, and therefore has even size.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

open Classical in
/-- The mixed-time-ordered positions lying in the external component. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalMixedPositions
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : Finset (Fin (2 * (2 * n + 1))) :=
  Finset.univ.filter fun p => ¬ d.1.LegIsVacuum (mixedTimeAmbientPositionEquiv τ τ' σ p)

open Classical in
theorem FixedExternalTwoPointWickDiagram.mem_externalMixedPositions_iff
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    p ∈ d.externalMixedPositions τ τ' σ ↔
      ¬ d.1.LegIsVacuum (mixedTimeAmbientPositionEquiv τ τ' σ p) := by
  simp [FixedExternalTwoPointWickDiagram.externalMixedPositions]

/-- **The external positions are closed under the pairing.** A contraction never joins the external
component to a vacuum component. -/
theorem FixedExternalTwoPointWickDiagram.partner_mem_externalMixedPositions
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1)))
    (hp : p ∈ d.externalMixedPositions τ τ' σ) :
    (d.pairingInMixedOrder τ τ' σ).partner p ∈ d.externalMixedPositions τ τ' σ := by
  rw [d.mem_externalMixedPositions_iff] at hp ⊢
  rw [d.mixedTimeAmbientPositionEquiv_partner τ τ' σ p]
  intro hvac
  exact hp ((d.1.legIsVacuum_partner_iff _).1 hvac)

/-- **The external positions come in pairs.** -/
theorem FixedExternalTwoPointWickDiagram.even_card_externalMixedPositions
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Even (d.externalMixedPositions τ τ' σ).card :=
  (d.pairingInMixedOrder τ τ' σ).even_card_of_partner_mem
    (d.partner_mem_externalMixedPositions τ τ' σ)

/-- The number of pairs the external component carries. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPairCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℕ :=
  (d.externalMixedPositions τ τ' σ).card / 2

theorem FixedExternalTwoPointWickDiagram.card_externalMixedPositions
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (d.externalMixedPositions τ τ' σ).card = 2 * d.externalPairCount τ τ' σ :=
  (Nat.mul_div_cancel' (d.even_card_externalMixedPositions τ τ' σ).two_dvd).symm

theorem FixedExternalTwoPointWickDiagram.externalPairCount_le
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : d.externalPairCount τ τ' σ ≤ 2 * n + 1 := by
  have hle : (d.externalMixedPositions τ τ' σ).card ≤ 2 * (2 * n + 1) := by
    simpa using Finset.card_le_univ (d.externalMixedPositions τ τ' σ)
  rw [d.card_externalMixedPositions] at hle
  omega

theorem FixedExternalTwoPointWickDiagram.card_compl_externalMixedPositions
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (d.externalMixedPositions τ τ' σ)ᶜ.card =
      2 * (2 * n + 1 - d.externalPairCount τ τ' σ) := by
  have hcompl : (d.externalMixedPositions τ τ' σ)ᶜ.card =
      2 * (2 * n + 1) - (d.externalMixedPositions τ τ' σ).card := by
    simpa using Finset.card_compl (d.externalMixedPositions τ τ' σ)
  rw [hcompl, d.card_externalMixedPositions]
  have := d.externalPairCount_le τ τ' σ
  omega

/-- **The splitting of the mixed-time positions into external and vacuum.**

Both parts are enumerated by increasing time, so the crossing-sign factorization applies with
nothing to route around. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPositionSplitting
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Combinatorics.PositionSplitting (d.externalPairCount τ τ' σ)
      (2 * n + 1 - d.externalPairCount τ τ' σ) (2 * n + 1) :=
  Combinatorics.monotonePositionSplitting (d.externalMixedPositions τ τ' σ)
    (d.card_externalMixedPositions τ τ' σ) (d.card_compl_externalMixedPositions τ τ' σ)

/-- **The mixed-order pairing is split by it.** No contraction joins the external component to a
vacuum component. -/
theorem FixedExternalTwoPointWickDiagram.isSplit_externalPositionSplitting
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder τ τ' σ).IsSplit (d.externalPositionSplitting τ τ' σ) := by
  intro k
  have hmem : (d.externalPositionSplitting τ τ' σ) (Sum.inl k) ∈
      d.externalMixedPositions τ τ' σ := by
    rw [FixedExternalTwoPointWickDiagram.externalPositionSplitting,
      Combinatorics.monotonePositionSplitting_inl]
    exact ((d.externalMixedPositions τ τ' σ).orderIsoOfFin
      (d.card_externalMixedPositions τ τ' σ) k).2
  have hpartner := d.partner_mem_externalMixedPositions τ τ' σ _ hmem
  obtain ⟨l, hl⟩ := ((d.externalMixedPositions τ τ' σ).orderIsoOfFin
    (d.card_externalMixedPositions τ τ' σ)).surjective ⟨_, hpartner⟩
  refine ⟨l, ?_⟩
  rw [FixedExternalTwoPointWickDiagram.externalPositionSplitting,
    Combinatorics.monotonePositionSplitting_inl]
  exact congrArg Subtype.val hl.symm

theorem FixedExternalTwoPointWickDiagram.externalPairCount_add
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.externalPairCount τ τ' σ + (2 * n + 1 - d.externalPairCount τ τ' σ) = 2 * n + 1 := by
  have := d.externalPairCount_le τ τ' σ
  omega

/-- **The crossing weight splits into external and vacuum.**

The between-part crossings are entirely carried by the sign of the permutation interleaving the two
parts; within-part crossings stay with their part. Both embeddings are monotone because the parts
are enumerated by increasing time, which is exactly what
`neg_one_pow_crossingCount_eq_of_isSplit` assumes. -/
theorem FixedExternalTwoPointWickDiagram.neg_one_pow_crossingCount_pairingInMixedOrder
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (-1 : ℤˣ) ^ (d.pairingInMixedOrder τ τ' σ).crossingCount =
      Equiv.Perm.sign
          ((splitBlockEquiv (d.externalPairCount_add τ τ' σ)).trans
            (d.externalPositionSplitting τ τ' σ)) *
        ((-1) ^ ((d.pairingInMixedOrder τ τ' σ).splitLeft
              (d.externalPositionSplitting τ τ' σ)
              (d.isSplit_externalPositionSplitting τ τ' σ)).crossingCount *
          (-1) ^ ((d.pairingInMixedOrder τ τ' σ).splitRight
              (d.externalPositionSplitting τ τ' σ)
              (d.isSplit_externalPositionSplitting τ τ' σ)).crossingCount) :=
  neg_one_pow_crossingCount_eq_of_isSplit
    (d.externalPositionSplitting τ τ' σ) (d.externalPairCount_add τ τ' σ)
    (d.isSplit_externalPositionSplitting τ τ' σ)
    (strictMono_monotonePositionSplitting_inl _ _ _)
    (strictMono_monotonePositionSplitting_inr _ _ _)

/-- The external component's own pairing, in mixed-time order. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPairingPiece
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : Pairing (d.externalPairCount τ τ' σ) :=
  (d.pairingInMixedOrder τ τ' σ).splitLeft (d.externalPositionSplitting τ τ' σ)
    (d.isSplit_externalPositionSplitting τ τ' σ)

/-- The vacuum components' pairing, in mixed-time order. -/
noncomputable def FixedExternalTwoPointWickDiagram.vacuumPairingPiece
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : Pairing (2 * n + 1 - d.externalPairCount τ τ' σ) :=
  (d.pairingInMixedOrder τ τ' σ).splitRight (d.externalPositionSplitting τ τ' σ)
    (d.isSplit_externalPositionSplitting τ τ' σ)

/-- The sign of the permutation interleaving the external and vacuum positions. It depends on the
splitting alone, not on the pairing. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalVacuumInterleaveSign
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  ((Equiv.Perm.sign ((splitBlockEquiv (d.externalPairCount_add τ τ' σ)).trans
    (d.externalPositionSplitting τ τ' σ)) : ℤ) : ℂ)

/-- The complex form of the crossing-weight split. -/
theorem FixedExternalTwoPointWickDiagram.neg_one_pow_crossingCount_complex
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (-1 : ℂ) ^ (d.pairingInMixedOrder τ τ' σ).crossingCount =
      d.externalVacuumInterleaveSign τ τ' σ *
        ((-1 : ℂ) ^ (d.externalPairingPiece τ τ' σ).crossingCount *
          (-1 : ℂ) ^ (d.vacuumPairingPiece τ τ' σ).crossingCount) := by
  have h := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ))
    (d.neg_one_pow_crossingCount_pairingInMixedOrder τ τ' σ)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  simpa [FixedExternalTwoPointWickDiagram.externalVacuumInterleaveSign,
    FixedExternalTwoPointWickDiagram.externalPairingPiece,
    FixedExternalTwoPointWickDiagram.vacuumPairingPiece] using h

end Fermionic
end SecondQuantization
