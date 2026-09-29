import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.Amplitude
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.ComponentFactorization
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticDysonExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteExpectationRecursion

set_option linter.style.header false

/-!
# Bosonic quartic Dyson-to-Wick bridge

The physical finite-order Dyson coefficient of a finitely supported quartic interaction is already a
finite sum of bare vertex-sequence operators with scalar ordered-simplex coefficients. The bosonic
thermal-field bridge identifies each bare vertex-sequence operator with an ordered product of free
thermal fields, whose convergence-aware Gibbs expectation has the concrete Bloch--de Dominicis
pairing expansion.

This file composes those existing boundaries. The ordered-simplex time integration remains entirely
inside `Common.quarticDysonSequenceCoeff`; no separate timed-diagram representation is introduced.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

variable {Mode : Type*} [Finite Mode]

/-- File-local classical equality matches the concrete free-thermal pair kernel. -/
local instance instDecidableEqQuarticDysonExpansion : DecidableEq Mode := Classical.decEq Mode

/-- The convergence-aware Gibbs expectation of a finite-order quartic Dyson coefficient is a finite
sum over support-valued vertex sequences and bosonic pairings. The scalar
`quarticDysonSequenceCoeff` carries the full ordered-simplex imaginary-time integration, while the
pairing evaluation is the existing static free-boson thermal Wick factor. -/
theorem freeGibbsDysonCoeff_quarticInteractionOn_eq_sum_pairingEvaluation
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (t : ℝ) :
    freeGibbsDysonCoeff ε β (quarticInteractionOn support g) n t =
      ∑ q : Fin n → ↥support,
        Common.quarticDysonSequenceCoeff ε g
            (fun i => (q i : QuarticVertexLabel Mode)) t *
          ∑ pairing : Pairing (2 * n),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily
                    (fun i => (q i : QuarticVertexLabel Mode)) a)
                  (quarticFreeThermalFieldFamily
                    (fun i => (q i : QuarticVertexLabel Mode)) b)) := by
  letI := Fintype.ofFinite Mode
  classical
  rw [freeGibbsDysonCoeff, dysonCoeff_quarticInteractionOn_eq_sum support ε g n t]
  have hsumm : ∀ q : Fin n → ↥support,
      freeGibbsSummable ε β
        (Common.quarticDysonSequenceCoeff ε g
            (fun i => (q i : QuarticVertexLabel Mode)) t •
          Common.quarticVertexSequenceOperator create annihilate
            (fun i => (q i : QuarticVertexLabel Mode))) := by
    intro q
    apply freeGibbsSummable_smul
    rw [← quarticFreeThermalOrderedProduct_eq_quarticVertexSequenceOperator]
    exact FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos _
  rw [freeGibbsExpectation_sum_of_summable ε β _ hsumm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [freeGibbsExpectation_smul]
  rw [← quarticFreeThermalOrderedProduct_eq_quarticVertexSequenceOperator,
    quarticFreeThermalOrderedProduct]
  have hwick := freeGibbsExpectation_eq_sum_pairing_concrete ε β hpos
    (2 * n) (quarticFreeThermalFieldFamily
      (fun i => (q i : QuarticVertexLabel Mode)))
  simpa only [Pairing.evaluation] using congrArg
    (fun z => Common.quarticDysonSequenceCoeff ε g
      (fun i => (q i : QuarticVertexLabel Mode)) t * z) hwick


/-- Fixed-order physical quartic Dyson diagram amplitude. The scalar Dyson sequence coefficient
contains the ordered-simplex time integration and coupling product, while the diagram contributes
one concrete bosonic thermal pairing value in the same vertex order. -/
noncomputable def QuarticDiagram.orderedDysonThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (order : Common.QuarticVertexOrder S) (t : ℝ) : ℂ :=
  Common.quarticDysonSequenceCoeff ε g (fun i => d.vertexLabel (order i)) t *
    QuarticDiagram.orderedThermalPairingValue ε β d order

private theorem freeGibbsDysonCoeff_quarticInteraction_eq_sum_pairingEvaluation [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (t : ℝ) :
    freeGibbsDysonCoeff ε β (quarticInteraction g) n t =
      ∑ q : Fin n → QuarticVertexLabel Mode,
        Common.quarticDysonSequenceCoeff ε g q t *
          ∑ pairing : Pairing (2 * n),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily q a)
                  (quarticFreeThermalFieldFamily q b)) := by
  let e :
      (Fin n → ↥(Finset.univ : Finset (QuarticVertexLabel Mode))) ≃
        (Fin n → QuarticVertexLabel Mode) :=
    { toFun := fun q i => q i
      invFun := fun q i => ⟨q i, Finset.mem_univ _⟩
      left_inv := by
        intro q
        funext i
        apply Subtype.ext
        rfl
      right_inv := by
        intro q
        rfl }
  let F : (Fin n → QuarticVertexLabel Mode) → ℂ := fun q =>
    Common.quarticDysonSequenceCoeff ε g q t *
      ∑ pairing : Pairing (2 * n),
        pairing.evaluation (pairing.weight .boson)
          (fun a b =>
            freeThermalPairValue ε β
              (quarticFreeThermalFieldFamily q a)
              (quarticFreeThermalFieldFamily q b))
  have h := freeGibbsDysonCoeff_quarticInteractionOn_eq_sum_pairingEvaluation
    (support := (Finset.univ : Finset (QuarticVertexLabel Mode))) ε β hpos g n t
  calc
    freeGibbsDysonCoeff ε β (quarticInteraction g) n t =
        freeGibbsDysonCoeff ε β
          (quarticInteractionOn (Finset.univ : Finset (QuarticVertexLabel Mode)) g) n t := by
            rfl
    _ = ∑ q : Fin n → ↥(Finset.univ : Finset (QuarticVertexLabel Mode)),
        Common.quarticDysonSequenceCoeff ε g
            (fun i => (q i : QuarticVertexLabel Mode)) t *
          ∑ pairing : Pairing (2 * n),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily
                    (fun i => (q i : QuarticVertexLabel Mode)) a)
                  (quarticFreeThermalFieldFamily
                    (fun i => (q i : QuarticVertexLabel Mode)) b)) := h
    _ = ∑ q : Fin n → ↥(Finset.univ : Finset (QuarticVertexLabel Mode)), F (e q) := by
      apply Finset.sum_congr rfl
      intro q _
      rfl
    _ = ∑ q : Fin n → QuarticVertexLabel Mode, F q := Equiv.sum_comp e F
    _ = ∑ q : Fin n → QuarticVertexLabel Mode,
        Common.quarticDysonSequenceCoeff ε g q t *
          ∑ pairing : Pairing (2 * n),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily q a)
                  (quarticFreeThermalFieldFamily q b)) := rfl

/-- The physical finite-order bosonic quartic Dyson coefficient is the sum of fixed-order physical
quartic diagram amplitudes. This is the canonical reindexing of the concrete
`vertex sequence × pairing` expansion through `Common.quarticDiagramEquivOrderedData`. -/
theorem freeGibbsDysonCoeff_quarticInteraction_eq_sum_orderedDysonThermalAmplitude [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} (S : Finset (Fin N))
    (order : Common.QuarticVertexOrder S) (t : ℝ) :
    freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t =
      ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
  classical
  rw [freeGibbsDysonCoeff_quarticInteraction_eq_sum_pairingEvaluation ε β hpos g S.card t]
  let F : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card → ℂ := fun x =>
    Common.quarticDysonSequenceCoeff ε g x.1 t *
      x.2.evaluation (x.2.weight .boson)
        (fun a b =>
          freeThermalPairValue ε β
            (quarticFreeThermalFieldFamily x.1 a)
            (quarticFreeThermalFieldFamily x.1 b))
  calc
    (∑ q : Fin S.card → QuarticVertexLabel Mode,
        Common.quarticDysonSequenceCoeff ε g q t *
          ∑ pairing : Pairing (2 * S.card),
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily q a)
                  (quarticFreeThermalFieldFamily q b))) =
      ∑ q : Fin S.card → QuarticVertexLabel Mode,
        ∑ pairing : Pairing (2 * S.card),
          Common.quarticDysonSequenceCoeff ε g q t *
            pairing.evaluation (pairing.weight .boson)
              (fun a b =>
                freeThermalPairValue ε β
                  (quarticFreeThermalFieldFamily q a)
                  (quarticFreeThermalFieldFamily q b)) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum]
    _ = ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card, F x := by
      rw [Fintype.sum_prod_type]
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        F (Common.quarticDiagramEquivOrderedData order d) :=
      (Common.sum_quarticDiagram_eq_sum_orderedData order F).symm
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      apply Finset.sum_congr rfl
      intro d _
      rfl


/-- Physical bosonic quartic Dyson diagram amplitude, summed over all global vertex orders.
The ordered-simplex regions associated with these orders are the pieces that shuffle-factorize over
connected components, so this physical amplitude is a sum rather than the static order average used
by `QuarticDiagram.thermalAmplitude`. -/
noncomputable def QuarticDiagram.dysonThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S) (t : ℝ) : ℂ :=
  ∑ order : Common.QuarticVertexOrder S,
    QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t

/-- The total physical quartic-diagram weight is the canonical vertex moment:
`|S|!` times the convergence-aware bosonic Dyson coefficient. The factorial is the number of
global vertex orders; unlike the static coefficientwise amplitude, it is not divided out because the
ordered-simplex shuffle sum is exactly what later factorizes over connected components. -/
theorem factorial_mul_freeGibbsDysonCoeff_quarticInteraction_eq_sum_dysonThermalAmplitude
    [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} (S : Finset (Fin N)) (t : ℝ) :
    (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t =
      ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.dysonThermalAmplitude ε β g d t := by
  classical
  calc
    (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t =
      ∑ _order : Common.QuarticVertexOrder S,
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t := by
          rw [Finset.sum_const, Finset.card_univ, Common.card_quarticVertexOrder]
          simp [nsmul_eq_mul]
    _ = ∑ order : Common.QuarticVertexOrder S,
        ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
          QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      apply Finset.sum_congr rfl
      intro order _
      exact
        freeGibbsDysonCoeff_quarticInteraction_eq_sum_orderedDysonThermalAmplitude
          ε β hpos g S order t
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        ∑ order : Common.QuarticVertexOrder S,
          QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t := by
      rw [Finset.sum_comm]
    _ = ∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
        QuarticDiagram.dysonThermalAmplitude ε β g d t := rfl


omit [Finite Mode] in
/-- The scalar quartic imaginary-time factor of an assembled global order is the family-shuffle
integrand of the corresponding component-local time factors. -/
private theorem QuarticDiagram.quarticVertexSequenceTimeFactor_assembleVertexOrder
    (ε : Mode → ℝ) {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) :
    Common.quarticVertexSequenceTimeFactor ε
        (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i)) τ =
      shuffle.ambientIntegrand
        (fun B : d.vertexGraph.componentPartitionOn.parts =>
          Common.quarticVertexSequenceTimeFactor ε
            (fun i => (d.restrictComponent B.2).vertexLabel (orders B i))) τ := by
  classical
  unfold Common.quarticVertexSequenceTimeFactor Combinatorics.FamilySlotShuffleTo.ambientIntegrand
  rw [← Equiv.prod_comp shuffle.slotEquiv]
  rw [Finset.prod_sigma']
  apply Fintype.prod_congr
  intro x
  obtain ⟨B, i⟩ := x
  simp only [Combinatorics.FamilySlotShuffleTo.timeAssignment_apply]
  rw [← d.restrictComponent_vertexLabel_componentOrder orders shuffle B i]

omit [Finite Mode] in
/-- For fixed component-local vertex orders, summing the physical ordered Dyson amplitude over all
order-preserving component shuffles gives the product of the corresponding component-local ordered
Dyson amplitudes. -/
private theorem QuarticDiagram.sum_shuffle_orderedDysonThermalAmplitude_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S)
    (orders : d.ComponentVertexOrders) (t : ℝ) :
    (∑ shuffle : d.ComponentShuffle,
      QuarticDiagram.orderedDysonThermalAmplitude ε β g d
        (d.assembleVertexOrder orders shuffle) t) =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g
          (d.restrictComponent B.2) (orders B) t := by
  classical
  let localIntegrand :
      ∀ B : d.vertexGraph.componentPartitionOn.parts,
        (Fin (B : Finset (Fin N)).card → ℝ) → ℂ :=
    fun B => Common.quarticVertexSequenceTimeFactor ε
      (fun i => (d.restrictComponent B.2).vertexLabel (orders B i))
  have hcard :
      (∑ B : d.vertexGraph.componentPartitionOn.parts, (B : Finset (Fin N)).card) = S.card := by
    rw [Finset.sum_coe_sort]
    exact d.vertexGraph.componentPartitionOn.sum_card_parts
  have htime :
      (∑ shuffle : d.ComponentShuffle,
        intervalIntegral.orderedSimplexIntegral S.card t
          (Common.quarticVertexSequenceTimeFactor ε
            (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i)))) =
        ∏ B : d.vertexGraph.componentPartitionOn.parts,
          intervalIntegral.orderedSimplexIntegral (B : Finset (Fin N)).card t
            (localIntegrand B) := by
    rw [show
      (fun shuffle : d.ComponentShuffle =>
        intervalIntegral.orderedSimplexIntegral S.card t
          (Common.quarticVertexSequenceTimeFactor ε
            (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i)))) =
        (fun shuffle : d.ComponentShuffle =>
          intervalIntegral.orderedSimplexIntegral S.card t
            (shuffle.ambientIntegrand localIntegrand)) by
      funext shuffle
      congr 1
      funext τ
      exact QuarticDiagram.quarticVertexSequenceTimeFactor_assembleVertexOrder
        ε d orders shuffle τ]
    exact Combinatorics.FamilySlotShuffleTo.sum_integral_eq_prod
      (fun B : d.vertexGraph.componentPartitionOn.parts => (B : Finset (Fin N)).card)
      S.card hcard t localIntegrand
      (fun B => intervalIntegral.Continuous.measurableLocallyBounded
        (Common.continuous_quarticVertexSequenceTimeFactor ε
          (fun i => (d.restrictComponent B.2).vertexLabel (orders B i))))
  simp only [QuarticDiagram.orderedDysonThermalAmplitude, Common.quarticDysonSequenceCoeff]
  have hpair (shuffle : d.ComponentShuffle) :
      QuarticDiagram.orderedThermalPairingValue ε β d
          (d.assembleVertexOrder orders shuffle) =
        ∏ B : d.vertexGraph.componentPartitionOn.parts,
          QuarticDiagram.orderedThermalPairingValue ε β
            (d.restrictComponent B.2) (orders B) :=
    QuarticDiagram.orderedThermalPairingValue_eq_prod_components ε β d orders shuffle
  simp_rw [hpair]
  have hvertex (shuffle : d.ComponentShuffle) :
      (∏ i, g (d.vertexLabel (d.assembleVertexOrder orders shuffle i))) = d.vertexWeight g := by
    unfold Common.QuarticDiagram.vertexWeight
    exact Equiv.prod_comp (d.assembleVertexOrder orders shuffle) (fun v => g (d.vertexLabel v))
  simp_rw [hvertex]
  let pairingProduct : ℂ :=
    ∏ B : d.vertexGraph.componentPartitionOn.parts,
      QuarticDiagram.orderedThermalPairingValue ε β
        (d.restrictComponent B.2) (orders B)
  rw [show
      (∑ shuffle : d.ComponentShuffle,
        (-1 : ℂ) ^ S.card * d.vertexWeight g *
            intervalIntegral.orderedSimplexIntegral S.card t
              (Common.quarticVertexSequenceTimeFactor ε
                (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i))) *
          pairingProduct) =
        ((-1 : ℂ) ^ S.card * d.vertexWeight g) *
          ((∑ shuffle : d.ComponentShuffle,
            intervalIntegral.orderedSimplexIntegral S.card t
              (Common.quarticVertexSequenceTimeFactor ε
                (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i)))) *
            pairingProduct) by
      calc
        _ = ∑ shuffle : d.ComponentShuffle,
            ((-1 : ℂ) ^ S.card * d.vertexWeight g) *
              (intervalIntegral.orderedSimplexIntegral S.card t
                (Common.quarticVertexSequenceTimeFactor ε
                  (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i))) *
                pairingProduct) := by
              apply Finset.sum_congr rfl
              intro shuffle _
              ring
        _ = ((-1 : ℂ) ^ S.card * d.vertexWeight g) *
            ∑ shuffle : d.ComponentShuffle,
              (intervalIntegral.orderedSimplexIntegral S.card t
                (Common.quarticVertexSequenceTimeFactor ε
                  (fun i => d.vertexLabel (d.assembleVertexOrder orders shuffle i))) *
                pairingProduct) := by
              rw [Finset.mul_sum]
        _ = _ := by
              rw [Finset.sum_mul]]
  rw [htime]
  rw [Common.QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_components d g]
  dsimp only [pairingProduct, localIntegrand]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro B _
  change
    ((-1 : ℂ) ^ (B : Finset (Fin N)).card *
        (d.restrictComponent B.2).vertexWeight g) *
        (_ * _) =
      (((-1 : ℂ) ^ (B : Finset (Fin N)).card *
        ∏ x, g ((d.restrictComponent B.2).vertexLabel (orders B x))) * _) * _
  rw [Common.QuarticDiagram.vertexWeight_eq_prod_vertexLabel_order
    (d.restrictComponent B.2) g (orders B)]
  ring

omit [Finite Mode] in
/-- The physical bosonic quartic Dyson diagram amplitude factors over the connected components of
the diagram. The proof reindexes global vertex orders into component-local orders and shuffles, then
uses the finite-family ordered-simplex shuffle identity for the time integrals. -/
theorem QuarticDiagram.dysonThermalAmplitude_eq_prod_components
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N : ℕ} {S : Finset (Fin N)}
    (d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S) (t : ℝ) :
    QuarticDiagram.dysonThermalAmplitude ε β g d t =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticDiagram.dysonThermalAmplitude ε β g (d.restrictComponent B.2) t := by
  classical
  unfold QuarticDiagram.dysonThermalAmplitude
  calc
    (∑ order : Common.QuarticVertexOrder S,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g d order t) =
      ∑ x : d.ComponentVertexOrders × d.ComponentShuffle,
        QuarticDiagram.orderedDysonThermalAmplitude ε β g d
          (d.assembleVertexOrder x.1 x.2) t := by
        rw [← Equiv.sum_comp d.componentOrderDecompositionEquiv.symm]
        rfl
    _ = ∑ orders : d.ComponentVertexOrders,
        ∑ shuffle : d.ComponentShuffle,
          QuarticDiagram.orderedDysonThermalAmplitude ε β g d
            (d.assembleVertexOrder orders shuffle) t := by
      rw [Fintype.sum_prod_type]
    _ = ∑ orders : d.ComponentVertexOrders,
        ∏ B : d.vertexGraph.componentPartitionOn.parts,
          QuarticDiagram.orderedDysonThermalAmplitude ε β g
            (d.restrictComponent B.2) (orders B) t := by
      apply Fintype.sum_congr
      intro orders
      exact QuarticDiagram.sum_shuffle_orderedDysonThermalAmplitude_eq_prod_components
        ε β g d orders t
    _ = ∏ B : d.vertexGraph.componentPartitionOn.parts,
        ∑ order : Common.QuarticVertexOrder (B : Finset (Fin N)),
          QuarticDiagram.orderedDysonThermalAmplitude ε β g
            (d.restrictComponent B.2) order t := by
      simpa using
        (Finset.prod_univ_sum
          (fun B : d.vertexGraph.componentPartitionOn.parts =>
            (Finset.univ : Finset (Common.QuarticVertexOrder (B : Finset (Fin N)))))
          (fun B order =>
            QuarticDiagram.orderedDysonThermalAmplitude ε β g
              (d.restrictComponent B.2) order t)).symm
    _ = ∏ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticDiagram.dysonThermalAmplitude ε β g (d.restrictComponent B.2) t := rfl

variable [Fintype Mode]

/-- The physical time-integrated bosonic quartic Dyson amplitude as a multiplicative diagram
weight. This is the diagrammatic moment forced by the convergence-aware Dyson coefficient, rather
than the static order-averaged thermal weight. -/
noncomputable def quarticDysonThermalDiagramMultiplicativeWeight
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (t : ℝ) {N : ℕ} :
    Combinatorics.MultiplicativeWeight
      (Common.quarticDiagramConnectedDecomposition (QuarticVertexLabel Mode) N) ℂ where
  objectWeight d := QuarticDiagram.dysonThermalAmplitude ε β g d t
  connectedWeight d := QuarticDiagram.dysonThermalAmplitude ε β g d.1 t
  weight_decompose d := by
    change QuarticDiagram.dysonThermalAmplitude ε β g d t =
      ∏ B : d.vertexGraph.componentPartitionOn.parts,
        QuarticDiagram.dysonThermalAmplitude ε β g (d.restrictComponentConnected B.2).1 t
    simpa only [Common.QuarticDiagram.restrictComponentConnected] using
      QuarticDiagram.dysonThermalAmplitude_eq_prod_components ε β g d t

/-- The normalized finite-set moment carried by the physical time-integrated bosonic quartic Dyson
diagrams. -/
noncomputable def quarticDysonThermalMoment
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (t : ℝ) {N : ℕ} :
    Combinatorics.NormalizedSetFunction (Fin N) ℂ :=
  (quarticDysonThermalDiagramMultiplicativeWeight ε β g t).normalizedObjectMoment

/-- The physical Dyson moment is exactly the factorial-normalized convergence-aware bosonic Dyson
coefficient. -/
theorem quarticDysonThermalMoment_eq_factorial_mul_freeGibbsDysonCoeff
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (g : QuarticVertexLabel Mode → ℂ) (t : ℝ) {N : ℕ} (S : Finset (Fin N)) :
    quarticDysonThermalMoment ε β g t S =
      (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t := by
  change
    (quarticDysonThermalDiagramMultiplicativeWeight ε β g t).objectMoment S =
      (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t
  change
    (∑ d : Common.QuarticDiagram (QuarticVertexLabel Mode) N S,
      QuarticDiagram.dysonThermalAmplitude ε β g d t) =
      (S.card.factorial : ℂ) *
        freeGibbsDysonCoeff ε β (quarticInteraction g) S.card t
  exact
    (factorial_mul_freeGibbsDysonCoeff_quarticInteraction_eq_sum_dysonThermalAmplitude
      ε β hpos g S t).symm

end
end Bosonic
end SecondQuantization
