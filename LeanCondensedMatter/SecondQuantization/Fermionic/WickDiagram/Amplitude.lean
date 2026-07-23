import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.Ordered
import LeanCondensedMatter.SecondQuantization.Fermionic.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.FreeBoltzmannWeight
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.Analysis.OrderedSimplexIntegral

set_option linter.style.header false

/-!
# Ordered-simplex quartic Wick-diagram amplitudes

Step 6 (PR 5c) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`): the
final sub-piece of PR 5's design, assembling `WickDiagram/Ordered.lean`'s vertex-order transport
and `Analysis/OrderedSimplexIntegral.lean`'s scalar iterated integral into a genuine
`ℂ`-valued amplitude `quarticWickDiagramAmplitude` for each `QuarticWickDiagram`. This is the
right-hand side PR 6's diagram-expansion theorem sums over:

```
dysonVertexMoment ε β (quarticInteraction g) S =
  ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
```

Connectivity (`WickDiagramConnected.lean`) is **not** imported here — the amplitude is defined for
every diagram, connected or not.

**Sign bookkeeping, spelled out because it is the easiest place for this construction to go
wrong.** Two structurally different signs appear, and neither should be conflated with the other
or with a `1/n!`:
- `(-1 : ℂ) ^ S.card`: the sign `dysonCoeff`'s recursion `Dₙ₊₁(τ) = -∫₀^τ V_I(σ) ∘ Dₙ(σ) dσ`
  bakes into the *n*-th coefficient itself.
- `pairing.weight Statistics.fermion = (-1) ^ pairing.crossingCount`: the fermionic Wick
  contraction sign, computed on the pairing *after* it has been transported onto the vertex
  order's slot enumeration (`QuarticWickDiagram.pairingInOrder`) — crossing count is not invariant
  under an arbitrary relabeling (`PerfectPairing/Relabel.lean`'s module docstring), so this must
  be recomputed there, never reused from `d.pairing.weight` directly.

No `1 / S.card!` appears: the sum below ranges over **all** vertex orders
(`QuarticVertexOrder S = Fin S.card ≃ ↥S`), not an average over them. The terms for different
vertex orders are generally *different* — a different order assigns different vertex labels to
the latest/outermost time slot, different time variables to each vertex, and transports the
pairing onto different ordered positions, so the individual ordered-simplex contributions differ
in general too. The sum runs over every assignment of the labelled vertices to the ordered time
slots, matching `dysonVertexMoment`'s own `S.card!` normalization (PR 6) — not a sum of `S.card!`
copies of a single value. No `1 / Z₀` appears either: `orderedQuarticPairValue` is already built
from `freeGibbsExpectation`, the *normalized* free Gibbs expectation, not a raw un-normalized
trace.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-! ## Local-leg operator semantics -/

/-- **The operator a vertex's local leg `Fin 4` stands for**, matching `WickDiagram.lean`'s fixed
local-leg convention `0 ↦ create₁, 1 ↦ create₂, 2 ↦ annihilate₂, 3 ↦ annihilate₁` exactly. -/
noncomputable def quarticLocalLegOperator (q : QuarticVertexLabel Mode) :
    Fin 4 → FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ![create q.create₁, create q.create₂, annihilate q.annihilate₂, annihilate q.annihilate₁]

/-- **The free-evolution eigenvalue shift** of a vertex's local leg — the exponent
`imaginaryTimeEvolve_quarticLocalLegOperator` below rescales that leg's operator by, matching each
local leg's sign convention (`+ε` for a creation operator, `-ε` for an annihilation operator). -/
noncomputable def quarticLocalLegEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) :
    Fin 4 → ℝ :=
  ![ε q.create₁, ε q.create₂, -ε q.annihilate₂, -ε q.annihilate₁]

omit [Fintype Mode] in
/-- **A local leg's operator evolves as a pure eigenvector** under `imaginaryTimeEvolve`, with
eigenvalue shift `quarticLocalLegEnergyShift`. The single fact tying `quarticLocalLegOperator`'s
four cases to `imaginaryTimeEvolve_create`/`imaginaryTimeEvolve_annihilate`. -/
theorem imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ) (q : QuarticVertexLabel Mode)
    (l : Fin 4) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) =
      Complex.exp (((τ * quarticLocalLegEnergyShift ε q l : ℝ) : ℂ)) •
        quarticLocalLegOperator q l := by
  fin_cases l <;>
    simp [quarticLocalLegOperator, quarticLocalLegEnergyShift, imaginaryTimeEvolve_create,
      imaginaryTimeEvolve_annihilate, mul_comm]

/-! ## Time-assigned operators, per vertex order -/

/-- **The operator at a flattened leg position, once a vertex order and a time assignment (one
real time per slot) are fixed**: look up which slot/local-leg the position corresponds to
(`orderedQuarticLegEquiv`), which vertex that slot's `order` picks out, and evolve that vertex's
local-leg operator to the slot's assigned time. -/
noncomputable def orderedQuarticLegOperator (ε : Mode → ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S) (τ : Fin S.card → ℝ)
    (p : Fin (2 * (2 * S.card))) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  let slotLeg := orderedQuarticLegEquiv S.card p
  imaginaryTimeEvolve ε (τ slotLeg.1) (quarticLocalLegOperator (d.vertexLabel (order slotLeg.1))
    slotLeg.2)

/-! ## Pair contraction values -/

/-- **The normalized free Gibbs pair value** of two flattened leg positions, at a fixed vertex
order and time assignment: `⟨C_a C_b⟩₀`, the operator-sequence-ordered (not time-ordered) free
Gibbs expectation the general Bloch–de Dominicis theorem's pairing terms use directly — *not*
`freeGibbsGreenFunction`, which carries its own extra minus sign and 2-operator time ordering that
would double up against `Pairing.weight`'s crossing sign. -/
noncomputable def orderedQuarticPairValue (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S) (τ : Fin S.card → ℝ)
    (a b : Fin (2 * (2 * S.card))) : ℂ :=
  freeGibbsExpectation ε β
    ((orderedQuarticLegOperator ε d order τ a).comp (orderedQuarticLegOperator ε d order τ b))

/-! ## Coupling weight -/

/-- **The diagram's coupling weight**: the product, over every vertex, of the coupling `g` at that
vertex's label. `quarticInteraction` itself carries no `1/2`/`1/4!` prefactor, so none is added
here either. -/
noncomputable def QuarticWickDiagram.couplingWeight {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (g : QuarticVertexLabel Mode → ℂ) : ℂ :=
  ∏ v : ↥S, g (d.vertexLabel v)

/-! ## Fixed-order Wick integrand and ordered-simplex contribution -/

/-- **The fixed-vertex-order Wick contraction integrand**: the fermionic crossing sign of the
diagram's pairing, transported onto `order`'s slot enumeration (`pairingInOrder` — *not* the sign
of the diagram's own stored pairing, since crossing count is not relabel-invariant), times the
product of pair values over that transported pairing's pairs. -/
noncomputable def QuarticWickDiagram.contractionIntegrand (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S)
    (τ : Fin S.card → ℝ) : ℂ :=
  (d.pairingInOrder order).weight Statistics.fermion *
    ∏ pr ∈ (d.pairingInOrder order).pairs, orderedQuarticPairValue ε β d order τ pr.1 pr.2

/-- **The fixed-vertex-order ordered-simplex contribution**: the contraction integrand, integrated
over the ordered simplex `0 ≤ τ_{S.card-1} ≤ ⋯ ≤ τ₀ ≤ β` (`orderedSimplexIntegral`). -/
noncomputable def QuarticWickDiagram.orderedSimplexContribution (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S) : ℂ :=
  intervalIntegral.orderedSimplexIntegral S.card β (d.contractionIntegrand ε β order)

/-! ## Continuity in the time assignment -/

/-- **Closed form of a pair value**: unfolds both evolved local-leg operators to their
`Complex.exp` eigenvalue-shift form (`imaginaryTimeEvolve_quarticLocalLegOperator`) and pulls both
scalars out of `freeGibbsExpectation` (`freeGibbsExpectation_smul`), leaving a fixed
(`τ`-independent) pair value of the two *bare* local-leg operators. The continuity lemma below is
this closed form's only consumer — the exponentials are visibly continuous (`fun_prop`) in `τ`
once written this way. -/
theorem orderedQuarticPairValue_eq (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S) (τ : Fin S.card → ℝ)
    (a b : Fin (2 * (2 * S.card))) :
    orderedQuarticPairValue ε β d order τ a b =
      Complex.exp
          ((τ (orderedQuarticLegEquiv S.card a).1 *
              quarticLocalLegEnergyShift ε
                (d.vertexLabel (order (orderedQuarticLegEquiv S.card a).1))
                (orderedQuarticLegEquiv S.card a).2 : ℝ) : ℂ) *
        Complex.exp
          ((τ (orderedQuarticLegEquiv S.card b).1 *
              quarticLocalLegEnergyShift ε
                (d.vertexLabel (order (orderedQuarticLegEquiv S.card b).1))
                (orderedQuarticLegEquiv S.card b).2 : ℝ) : ℂ) *
        freeGibbsExpectation ε β
          ((quarticLocalLegOperator
              (d.vertexLabel (order (orderedQuarticLegEquiv S.card a).1))
              (orderedQuarticLegEquiv S.card a).2).comp
            (quarticLocalLegOperator
              (d.vertexLabel (order (orderedQuarticLegEquiv S.card b).1))
              (orderedQuarticLegEquiv S.card b).2)) := by
  simp only [orderedQuarticPairValue, orderedQuarticLegOperator,
    imaginaryTimeEvolve_quarticLocalLegOperator, LinearMap.smul_comp, LinearMap.comp_smul,
    smul_smul, freeGibbsExpectation_smul]
  ring

/-- **A pair value is continuous in the time assignment `τ`** — directly from the closed form
`orderedQuarticPairValue_eq`: a product of two `Complex.exp`s of a continuous (coordinate-linear)
function of `τ`, times a `τ`-independent constant. -/
theorem continuous_orderedQuarticPairValue (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S)
    (a b : Fin (2 * (2 * S.card))) :
    Continuous (fun τ : Fin S.card → ℝ => orderedQuarticPairValue ε β d order τ a b) := by
  simp only [orderedQuarticPairValue_eq]
  fun_prop

/-- **The fixed-vertex-order Wick contraction integrand is continuous in `τ`** — a `τ`-independent
crossing-sign constant, times a finite product (over the transported pairing's pairs) of
`continuous_orderedQuarticPairValue`'s continuous pair values. -/
theorem continuous_contractionIntegrand (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S) :
    Continuous (d.contractionIntegrand ε β order) := by
  have heq : d.contractionIntegrand ε β order = fun τ =>
      (d.pairingInOrder order).weight Statistics.fermion *
        ∏ pr ∈ (d.pairingInOrder order).pairs, orderedQuarticPairValue ε β d order τ pr.1 pr.2 :=
    rfl
  rw [heq]
  exact continuous_const.mul
    (continuous_finsetProd _ fun pr _ => continuous_orderedQuarticPairValue ε β d order pr.1 pr.2)

/-! ## The diagram amplitude -/

/-- **The quartic Wick-diagram amplitude**: `(-1)^{S.card}` (the Dyson-recursion sign) times the
diagram's coupling weight, times the sum — over **every** vertex order, with no `1/S.card!` — of
that order's ordered-simplex contribution. See the module docstring for why neither sign may be
dropped, combined, or replaced by an average. -/
noncomputable def quarticWickDiagramAmplitude (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) : ℂ :=
  (-1 : ℂ) ^ S.card * d.couplingWeight g *
    ∑ order : QuarticVertexOrder S, d.orderedSimplexContribution ε β order

/-! ## Basic lemmas -/

/-- **There is exactly one vertex order on the empty vertex set** — both `Fin 0` and `↥(∅ :
Finset (Fin N))` are empty types, so `Equiv.equivOfIsEmpty` gives one, and any two equivs between
empty types agree (`Subsingleton.elim`). -/
instance QuarticVertexOrder.uniqueEmpty : Unique (QuarticVertexOrder (∅ : Finset (Fin N))) where
  default := by
    haveI : IsEmpty (↥(∅ : Finset (Fin N))) := Finset.isEmpty_coe_sort.2 rfl
    haveI : IsEmpty (Fin (Finset.card (∅ : Finset (Fin N)))) := by
      rw [Finset.card_empty]; infer_instance
    exact Equiv.equivOfIsEmpty (Fin (Finset.card (∅ : Finset (Fin N)))) _
  uniq _ := Subsingleton.elim _ _

/-- **The empty-vertex-set amplitude is `1`**, matching `dysonVertexMoment_empty` — the sign,
coupling product, and order sum all collapse trivially at `S = ∅`. -/
@[simp]
theorem quarticWickDiagramAmplitude_empty (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (d : QuarticWickDiagram Mode N (∅ : Finset (Fin N))) :
    quarticWickDiagramAmplitude ε β g d = 1 := by
  have hcard : (∅ : Finset (Fin N)).card = 0 := Finset.card_empty
  have hcontrib : ∀ order : QuarticVertexOrder (∅ : Finset (Fin N)),
      d.orderedSimplexContribution ε β order = 1 := by
    intro order
    simp only [QuarticWickDiagram.orderedSimplexContribution]
    simp [QuarticWickDiagram.contractionIntegrand, Common.BlochDeDominicis.Pairing.pairs,
      Common.BlochDeDominicis.Pairing.crossingCount]
  simp only [quarticWickDiagramAmplitude, QuarticWickDiagram.couplingWeight, hcard, pow_zero,
    one_mul]
  have hcoupling : ∏ v : (↥(∅ : Finset (Fin N))), g (d.vertexLabel v) = 1 := by
    have : IsEmpty (↥(∅ : Finset (Fin N))) := Finset.isEmpty_coe_sort.2 rfl
    exact Finset.prod_of_isEmpty _
  rw [hcoupling, one_mul, Finset.sum_congr rfl (fun order _ => hcontrib order),
    Finset.sum_const, Finset.card_univ, Fintype.card_unique]
  simp

end SecondQuantization
