import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.VertexLabel
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Statistics-independent quartic operator structure

The four local-leg modes, creation/annihilation kinds, free-energy shifts, and fixed operator order of
a number-conserving quartic vertex do not depend on exchange statistics.  This module packages that
shared structure while leaving concrete CAR/CCR relations in the fermionic and bosonic layers.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Mode Config : Type*}

/-- The creation/annihilation kind carried by a local quartic leg. -/
inductive QuarticLocalLegKind where
  | create
  | annihilate
  deriving DecidableEq

/-- The mode on which a local quartic leg acts, in fixed operator-composition order. -/
def quarticLocalLegMode (q : QuarticVertexLabel Mode) : Fin 4 → Mode :=
  ![q.create₁, q.create₂, q.annihilate₂, q.annihilate₁]

/-- The creation/annihilation kind of each local quartic leg. -/
def quarticLocalLegKind : Fin 4 → QuarticLocalLegKind :=
  ![.create, .create, .annihilate, .annihilate]

/-- Boolean compatibility view of `quarticLocalLegKind`. -/
def quarticLocalLegIsCreate : Fin 4 → Bool :=
  ![true, true, false, false]

/-- The free-energy shift of each local quartic leg. -/
def quarticLocalLegEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) : Fin 4 → ℝ :=
  ![ε q.create₁, ε q.create₂, -ε q.annihilate₂, -ε q.annihilate₁]

/-- The total free-energy shift of a quartic vertex. -/
def quarticVertexEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) : ℝ :=
  ε q.create₁ + ε q.create₂ - ε q.annihilate₁ - ε q.annihilate₂

/-- Local quartic-leg operators constructed from arbitrary creation and annihilation maps. -/
def quarticLocalLegOperator
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) : Fin 4 → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  ![create q.create₁, create q.create₂, annihilate q.annihilate₂, annihilate q.annihilate₁]

/-- The fixed ordered quartic vertex operator constructed from arbitrary ladder maps. -/
def quarticVertexOperator
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  (create q.create₁).comp
    ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))

/-- A finite quartic interaction constructed from arbitrary ladder maps. -/
def quarticInteraction [Fintype Mode]
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (g : QuarticVertexLabel Mode → ℂ) : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  ∑ q, g q • quarticVertexOperator create annihilate q

/-- A quartic vertex assembled from ladder eigenoperators evolves with their total energy shift. -/
theorem heisenbergEvolve_quarticVertexOperator
    (energy : Config → ℝ) (ε : Mode → ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) (τ : ℝ)
    (hcreate : ∀ i, heisenbergEvolve energy τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i)
    (hannihilate : ∀ i, heisenbergEvolve energy τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) :
    heisenbergEvolve energy τ (quarticVertexOperator create annihilate q) =
      Complex.exp ((τ : ℂ) * (quarticVertexEnergyShift ε q : ℂ)) •
        quarticVertexOperator create annihilate q := by
  simp only [quarticVertexOperator, heisenbergEvolve_comp]
  rw [hcreate, hcreate, hannihilate, hannihilate]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [quarticVertexEnergyShift]
  push_cast
  ring

/-- Diagonal Heisenberg evolution distributes over a finite quartic interaction. -/
theorem heisenbergEvolve_quarticInteraction [Fintype Mode]
    (energy : Config → ℝ) (τ : ℝ)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (g : QuarticVertexLabel Mode → ℂ) :
    heisenbergEvolve energy τ (quarticInteraction create annihilate g) =
      ∑ q, g q • heisenbergEvolve energy τ (quarticVertexOperator create annihilate q) := by
  rw [quarticInteraction]
  rw [heisenbergEvolve_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [heisenbergEvolve_smul]

end
end Common
end SecondQuantization
