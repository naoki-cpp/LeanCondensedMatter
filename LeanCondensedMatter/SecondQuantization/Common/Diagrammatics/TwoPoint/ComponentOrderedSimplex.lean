import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.Analysis.OrderedSimplex.FinCast
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentVertexProduct

set_option linter.style.header false

/-!
# Ordered-simplex shuffles over two-point diagram interaction components

The full components of a two-point diagram partition its interaction vertices, although the unique
external component also contains the two distinguished external vertices. This module therefore
uses the interaction part of every full component as its local ordered-simplex slot block.

An order-preserving shuffle interleaves those local interaction slots into the ambient interaction
slots. The generic finite-family shuffle identity then identifies the sum of shuffled ambient
ordered-simplex integrals with the product of the component-local ordered-simplex integrals.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Number of interaction-time slots belonging to one full component. -/
abbrev TwoPointDiagram.interactionComponentSize {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) : ℕ :=
  (TwoPointDiagram.interactionPart
    (B : Finset (TwoPointVertex S))).card

/-- An order-preserving interleaving of all component-local interaction slots into the ambient
interaction-time slots. -/
structure TwoPointDiagram.ComponentInteractionShuffle {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) where
  /-- Equivalence between component-local interaction slots and ambient interaction slots. -/
  slotEquiv :
    (Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) ≃ Fin S.card
  strictMono : ∀ B, StrictMono (fun i => slotEquiv ⟨B, i⟩)

@[ext]
theorem TwoPointDiagram.ComponentInteractionShuffle.ext {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    {σ τ : d.ComponentInteractionShuffle}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- The component-local interaction-slot family has the ambient number of interaction vertices. -/
theorem TwoPointDiagram.sum_interactionComponentSize {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (∑ B : d.componentPartition.parts, d.interactionComponentSize B) = S.card := by
  calc
    (∑ B : d.componentPartition.parts, d.interactionComponentSize B) =
        Fintype.card
          (Σ B : d.componentPartition.parts,
            ↥(TwoPointDiagram.interactionPart
              (B : Finset (TwoPointVertex S)))) := by
      simp [Fintype.card_sigma]
    _ = Fintype.card ↥S :=
      Fintype.card_congr d.interactionVertexComponentEquiv.symm
    _ = S.card := Fintype.card_coe S

/-- Two-point component interaction shuffles form a finite type. -/
instance TwoPointDiagram.ComponentInteractionShuffle.instFintype
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Fintype d.ComponentInteractionShuffle :=
  Fintype.ofInjective
    (fun shuffle : d.ComponentInteractionShuffle => shuffle.slotEquiv)
    (fun _ _ h => TwoPointDiagram.ComponentInteractionShuffle.ext h)

/-- Restrict an ambient interaction-time assignment to the local slots of one full component. -/
def TwoPointDiagram.interactionComponentTimeAssignment {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts) :
    Fin (d.interactionComponentSize B) → ℝ :=
  fun i => τ (shuffle.slotEquiv ⟨B, i⟩)

@[simp]
theorem TwoPointDiagram.interactionComponentTimeAssignment_apply {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (i : Fin (d.interactionComponentSize B)) :
    d.interactionComponentTimeAssignment shuffle τ B i =
      τ (shuffle.slotEquiv ⟨B, i⟩) :=
  rfl

/-- Restricting ambient interaction times to one component is continuous. -/
theorem TwoPointDiagram.continuous_interactionComponentTimeAssignment
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (B : d.componentPartition.parts) :
    Continuous (fun τ : Fin S.card → ℝ =>
      d.interactionComponentTimeAssignment shuffle τ B) := by
  exact continuous_pi fun i => continuous_apply (shuffle.slotEquiv ⟨B, i⟩)

/-- Product of component-local interaction-time integrands after embedding their coordinates by a
shuffle. -/
def TwoPointDiagram.interactionComponentShuffleIntegrand
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) : ℂ :=
  ∏ B, componentIntegrand B
    (d.interactionComponentTimeAssignment shuffle τ B)

/-- A product of continuous component-local interaction-time integrands remains continuous after
shuffling. -/
theorem TwoPointDiagram.continuous_interactionComponentShuffleIntegrand
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    Continuous (d.interactionComponentShuffleIntegrand shuffle componentIntegrand) := by
  unfold TwoPointDiagram.interactionComponentShuffleIntegrand
  exact continuous_finsetProd _ fun B _ =>
    (hcomponent B).comp
      (d.continuous_interactionComponentTimeAssignment shuffle B)

/-- An enumeration of the full component parts of a two-point diagram by `Fin k`. -/
structure TwoPointDiagram.FiniteInteractionComponentPresentation
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (k : ℕ) where
  /-- Equivalence between finite component indices and full component parts. -/
  partsEquiv : Fin k ≃ d.componentPartition.parts

namespace TwoPointDiagram.FiniteInteractionComponentPresentation

/-- The canonical finite presentation obtained by enumerating the component type. -/
def canonical {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.FiniteInteractionComponentPresentation
      (Fintype.card d.componentPartition.parts) where
  partsEquiv := (Fintype.equivFin d.componentPartition.parts).symm

/-- Number of local interaction slots in the component with finite index `i`. -/
abbrev size {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k) (i : Fin k) : ℕ :=
  d.interactionComponentSize (p.partsEquiv i)

/-- Reindex finite-family local slots by the chosen component enumeration. -/
def localSlotEquiv {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k) :
    (Σ i : Fin k, Fin (p.size i)) ≃
      (Σ B : d.componentPartition.parts, Fin (d.interactionComponentSize B)) :=
  p.partsEquiv.sigmaCongrLeft
    (β := fun B : d.componentPartition.parts => Fin (d.interactionComponentSize B))

@[simp]
theorem localSlotEquiv_apply {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k)
    (i : Fin k) (j : Fin (p.size i)) :
    p.localSlotEquiv ⟨i, j⟩ = ⟨p.partsEquiv i, j⟩ := by
  simp [localSlotEquiv]

@[simp]
theorem localSlotEquiv_symm_apply {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k)
    (i : Fin k) (j : Fin (p.size i)) :
    p.localSlotEquiv.symm ⟨p.partsEquiv i, j⟩ = ⟨i, j⟩ := by
  apply p.localSlotEquiv.injective
  simp

/-- The sum of the enumerated interaction-component sizes is the ambient interaction order. -/
theorem totalCard {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k) :
    (∑ i, p.size i) = S.card := by
  calc
    (∑ i, p.size i) =
        ∑ B : d.componentPartition.parts, d.interactionComponentSize B := by
      simpa [Fintype.card_sigma] using Fintype.card_congr p.localSlotEquiv
    _ = S.card := d.sum_interactionComponentSize

/-- Transport a generic finite-family slot shuffle to a two-point component interaction shuffle. -/
def toComponentShuffle {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k)
    (shuffle : FamilySlotShuffle p.size) : d.ComponentInteractionShuffle where
  slotEquiv := p.localSlotEquiv.symm.trans
    (shuffle.slotEquiv.trans (finCongr p.totalCard))
  strictMono := by
    intro B
    obtain ⟨i, rfl⟩ := p.partsEquiv.surjective B
    intro a b hab
    change (finCongr p.totalCard)
        (shuffle.slotEquiv (p.localSlotEquiv.symm ⟨p.partsEquiv i, a⟩)) <
      (finCongr p.totalCard)
        (shuffle.slotEquiv (p.localSlotEquiv.symm ⟨p.partsEquiv i, b⟩))
    rw [p.localSlotEquiv_symm_apply, p.localSlotEquiv_symm_apply]
    exact (strictMono_finCongr p.totalCard) (shuffle.strictMono i hab)

/-- Read a generic finite-family slot shuffle from a two-point component interaction shuffle. -/
def fromComponentShuffle {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k)
    (shuffle : d.ComponentInteractionShuffle) : FamilySlotShuffle p.size where
  slotEquiv := p.localSlotEquiv.trans
    (shuffle.slotEquiv.trans (finCongr p.totalCard).symm)
  strictMono := by
    intro i a b hab
    have hcast : StrictMono (finCongr p.totalCard).symm := by
      simpa using strictMono_finCongr p.totalCard.symm
    change (finCongr p.totalCard).symm
        (shuffle.slotEquiv (p.localSlotEquiv ⟨i, a⟩)) <
      (finCongr p.totalCard).symm
        (shuffle.slotEquiv (p.localSlotEquiv ⟨i, b⟩))
    rw [p.localSlotEquiv_apply, p.localSlotEquiv_apply]
    exact hcast (shuffle.strictMono (p.partsEquiv i) hab)

/-- Generic finite-family slot shuffles and two-point component interaction shuffles are equivalent
under a finite presentation. -/
def componentShuffleEquiv {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k) :
    FamilySlotShuffle p.size ≃ d.ComponentInteractionShuffle where
  toFun := p.toComponentShuffle
  invFun := p.fromComponentShuffle
  left_inv shuffle := by
    apply FamilySlotShuffle.ext
    ext x
    simp [toComponentShuffle, fromComponentShuffle]
  right_inv shuffle := by
    apply TwoPointDiagram.ComponentInteractionShuffle.ext
    ext x
    simp [toComponentShuffle, fromComponentShuffle]

/-- The component-shuffle integrand transported from a generic finite-family shuffle is its family
integrand, up to the global finite-dimension cast. -/
theorem interactionComponentShuffleIntegrand_toComponentShuffle
    {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k)
    (shuffle : FamilySlotShuffle p.size)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) :
    d.interactionComponentShuffleIntegrand
        (p.toComponentShuffle shuffle) componentIntegrand τ =
      shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))
        (fun j => τ (finCongr p.totalCard j)) := by
  classical
  unfold TwoPointDiagram.interactionComponentShuffleIntegrand
    FamilySlotShuffle.integrand
  calc
    (∏ B : d.componentPartition.parts,
        componentIntegrand B
          (d.interactionComponentTimeAssignment
            (p.toComponentShuffle shuffle) τ B)) =
      ∏ i : Fin k,
        componentIntegrand (p.partsEquiv i)
          (d.interactionComponentTimeAssignment
            (p.toComponentShuffle shuffle) τ (p.partsEquiv i)) := by
      symm
      refine Fintype.prod_equiv p.partsEquiv _ _ ?_
      intro i
      rfl
    _ = ∏ i : Fin k,
        componentIntegrand (p.partsEquiv i)
          (shuffle.timeAssignment (fun j => τ (finCongr p.totalCard j)) i) := by
      apply congrArg (fun h : Fin k → ℂ => ∏ i, h i)
      funext i
      apply congrArg (componentIntegrand (p.partsEquiv i))
      funext j
      simp [TwoPointDiagram.interactionComponentTimeAssignment,
        toComponentShuffle, FamilySlotShuffle.timeAssignment]

/-- One transported component-shuffle ordered-simplex term is the corresponding generic family
term. -/
theorem orderedSimplexIntegral_toComponentShuffle
    {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k)
    (shuffle : FamilySlotShuffle p.size) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ) :
    orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand
          (p.toComponentShuffle shuffle) componentIntegrand) =
      orderedSimplexIntegral (∑ i, p.size i) β
        (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) := by
  calc
    orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand
          (p.toComponentShuffle shuffle) componentIntegrand) =
      orderedSimplexIntegral S.card β (fun τ =>
        shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))
          (fun j => τ (finCongr p.totalCard j))) := by
      apply orderedSimplexIntegral_congr
      intro τ
      exact p.interactionComponentShuffleIntegrand_toComponentShuffle
        shuffle componentIntegrand τ
    _ = orderedSimplexIntegral (∑ i, p.size i) β
        (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) := by
      symm
      simpa using intervalIntegral.orderedSimplexIntegral_cast p.totalCard β
        (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i)))

/-- Reindex the finite sum over two-point component interaction shuffles as a sum over generic
finite-family shuffles. -/
theorem sum_componentShuffle_orderedSimplexIntegral
    {S : Finset (Fin N)}
    {d : TwoPointDiagram ExternalLabel InternalLabel N S} {k : ℕ}
    (p : d.FiniteInteractionComponentPresentation k) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ) :
    (∑ shuffle : d.ComponentInteractionShuffle,
      orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand shuffle componentIntegrand)) =
      ∑ shuffle : FamilySlotShuffle p.size,
        orderedSimplexIntegral (∑ i, p.size i) β
          (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) := by
  rw [← Equiv.sum_comp p.componentShuffleEquiv]
  apply Finset.sum_congr rfl
  intro shuffle _hshuffle
  change orderedSimplexIntegral S.card β
      (d.interactionComponentShuffleIntegrand
        (p.toComponentShuffle shuffle) componentIntegrand) = _
  exact p.orderedSimplexIntegral_toComponentShuffle shuffle β componentIntegrand

end TwoPointDiagram.FiniteInteractionComponentPresentation

/-- Finite-family ordered-simplex shuffle product identity for the interaction parts of all full
two-point components. -/
theorem TwoPointDiagram.sum_componentInteractionShuffle_orderedSimplexIntegral_eq_prod
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    (∑ shuffle : d.ComponentInteractionShuffle,
      orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand shuffle componentIntegrand)) =
      ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (d.interactionComponentSize B) β
          (componentIntegrand B) := by
  classical
  let p := TwoPointDiagram.FiniteInteractionComponentPresentation.canonical d
  calc
    (∑ shuffle : d.ComponentInteractionShuffle,
        orderedSimplexIntegral S.card β
          (d.interactionComponentShuffleIntegrand shuffle componentIntegrand)) =
      ∑ shuffle : FamilySlotShuffle p.size,
        orderedSimplexIntegral (∑ i, p.size i) β
          (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) :=
      p.sum_componentShuffle_orderedSimplexIntegral β componentIntegrand
    _ = ∏ i,
        orderedSimplexIntegral (p.size i) β
          (componentIntegrand (p.partsEquiv i)) :=
      FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod
        _ p.size β (fun i => componentIntegrand (p.partsEquiv i))
        (fun i => hcomponent (p.partsEquiv i))
    _ = ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (d.interactionComponentSize B) β
          (componentIntegrand B) := by
      refine Fintype.prod_equiv p.partsEquiv _ _ ?_
      intro i
      rfl

end

end Common
end SecondQuantization
