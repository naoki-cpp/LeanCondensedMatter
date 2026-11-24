import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedTimeOrdering

set_option linter.style.header false

/-!
# Fixed-time amplitudes for arbitrary external insertions

The canonical fixed flattened leg order is transported to mixed imaginary-time order by
`externalInsertionStandardToMixedAtomicPositionEquiv`. Its permutation sign supplies the fermionic
ordering factor for the full atomic field list. Quartic interaction vertices contribute four
consecutive legs, so no separate interaction-order sign is introduced here.

The fixed-time amplitude is this ordering sign times the generic interaction-vertex weight and the
mixed-time pairing evaluation from `TimedField`.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Fixed-time amplitude of an arbitrary external-insertion Wick diagram. -/
noncomputable def ExternalInsertionWickDiagram.fixedTimeAmplitude {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  externalInsertionMixedAtomicOrderSign externalTime σ *
    d.vertexWeight g *
      d.mixedPairingValue ε β externalTime σ

/-- Dyson-signed fixed-time amplitude. The perturbative factor `(-1)^n` is kept separate from
the mixed-time ordering sign carried by `fixedTimeAmplitude`. -/
noncomputable def ExternalInsertionWickDiagram.dysonFixedTimeAmplitude {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  (-1 : ℂ) ^ n * d.fixedTimeAmplitude ε β g externalTime σ


/-- The complete fixed-time physical Wick diagram amplitude, including
its fermionic ordering sign, interaction coupling product, and oriented
free-Gibbs pairing evaluation, is invariant under any permutation of
quartic interaction vertices and their time/label assignments, provided
the interaction times are injective. -/
theorem ExternalInsertionWickDiagram.slotCongr_fixedTimeAmplitude_eq_of_injective
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    ExternalInsertionWickDiagram.fixedTimeAmplitude (d.slotCongr e) ε β g externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1) =
      d.fixedTimeAmplitude ε β g externalTime σ := by
  simp only [ExternalInsertionWickDiagram.fixedTimeAmplitude,
    externalInsertionMixedAtomicOrderSign_eq_of_externalTimes externalTime
      (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1) σ,
    d.slotCongr_vertexWeight e g,
    d.slotCongr_mixedPairingValue_eq_of_injective e ε β externalTime σ hσ]

/-- **Full physical Dyson-signed fixed-time amplitude covariance.**
On every strict interaction-time chamber, arbitrary relabeling of
quartic interaction vertices has no effect on the physical amplitude;
the same Dyson factor `(-1)^n` multiplies both sides.

No equality at coincident interaction-vertex times is asserted. Such
collisions are excluded by the strict ordered-simplex congruence
theorem when passing to integrated Dyson contributions. -/
theorem ExternalInsertionWickDiagram.slotCongr_dysonFixedTimeAmplitude_eq_of_injective
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (e : ↥(Finset.univ : Finset (Fin n)) ≃
      ↥(Finset.univ : Finset (Fin n)))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (d.slotCongr e) ε β g externalTime
        (σ ∘ fun v => (e.symm ⟨v, Finset.mem_univ v⟩).1) =
      d.dysonFixedTimeAmplitude ε β g externalTime σ := by
  simp only [ExternalInsertionWickDiagram.dysonFixedTimeAmplitude,
    d.slotCongr_fixedTimeAmplitude_eq_of_injective e ε β g externalTime σ hσ]

end Fermionic
end SecondQuantization
