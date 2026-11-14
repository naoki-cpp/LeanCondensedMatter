import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField
import Mathlib.GroupTheory.Perm.Sign

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

/-- An arbitrary permutation of **quartic interaction vertices** induces
an *even* permutation of their flattened atomic legs. The four local
legs of each vertex retain their order. This is the parity fact
needed to cancel relabeling signs in physical fermionic amplitudes. -/
theorem quarticVertexBlockPermutation_sign_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) :
    Equiv.Perm.sign (p.prodCongr (Equiv.refl (Fin 4))) = 1 := by
  classical
  have hperm :
      p.prodCongr (Equiv.refl (Fin 4)) =
        Equiv.prodCongrLeft (fun _ : Fin 4 => p) := by
    ext ⟨v, l⟩
    rfl
  rw [hperm, Equiv.Perm.sign_prodCongrLeft]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    (Equiv.Perm.sign p) ^ 4 =
        ((Equiv.Perm.sign p) ^ 2) ^ 2 := by
          rw [← pow_mul]
    _ = 1 := by simp

/-- The actual flattened-leg transport of an arbitrary external-insertion
diagram is even under any bijection of its interaction vertices.
External insertion positions are fixed and each interaction contributes
four legs, so this does not depend on external field count or the
interaction-subset geometry. -/
theorem externalInsertionLegCongr_sign_eq_one
    {E n : ℕ} {T : Finset (Fin n)}
    (e : ↥T ≃ ↥T) :
    Equiv.Perm.sign (externalInsertionLegCongr (E := E) e) = 1 := by
  classical
  let p : Equiv.Perm (Fin (2 * E) ⊕ (↥T × Fin 4)) :=
    (Equiv.refl (Fin (2 * E))).sumCongr
      (e.prodCongr (Equiv.refl (Fin 4)))
  have hcongr :
      externalInsertionLegCongr (E := E) e =
        (externalInsertionLegEquiv E T).symm.permCongr p := by
    rfl
  rw [hcongr, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]
  simp [quarticVertexBlockPermutation_sign_eq_one]

/-- Fermionic sign of the permutation from fixed flattened atomic order to mixed-time atomic order. -/
noncomputable def externalInsertionMixedAtomicOrderSign {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  ((Equiv.Perm.sign
    (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) : ℤ) : ℂ)

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

end Fermionic
end SecondQuantization
