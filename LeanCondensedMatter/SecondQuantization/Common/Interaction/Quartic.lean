import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Statistics-independent quartic interaction structure

A number-conserving quartic interaction vertex carries two creation modes and two annihilation modes.
The local-leg ordering, generic ladder-map operator constructors, finite-support interaction sums, and
free-energy shifts are independent of particle statistics and imaginary-time evolution.

A quartic interaction only needs finitely many nonzero vertex labels, not a finite ambient mode type.
`quarticInteractionOn` takes that finite support explicitly. The finite-mode constructor
`quarticInteraction` is its `Finset.univ` specialization.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Mode Config : Type*}

/-- The four mode labels of a number-conserving quartic interaction vertex. -/
structure QuarticVertexLabel (Mode : Type*) where
  /-- The first creation mode. -/
  create₁ : Mode
  /-- The second creation mode. -/
  create₂ : Mode
  /-- The first annihilation mode. -/
  annihilate₁ : Mode
  /-- The second annihilation mode. -/
  annihilate₂ : Mode
  deriving DecidableEq, Fintype

/-- The creation/annihilation kind carried by a local quartic leg. -/
inductive QuarticLocalLegKind where
  | create
  | annihilate
  deriving DecidableEq

/-- The mode on which a local quartic leg acts, in fixed operator-composition order. -/
abbrev quarticLocalLegMode (q : QuarticVertexLabel Mode) : Fin 4 → Mode :=
  ![q.create₁, q.create₂, q.annihilate₂, q.annihilate₁]

/-- The creation/annihilation kind of each local quartic leg. -/
abbrev quarticLocalLegKind : Fin 4 → QuarticLocalLegKind :=
  ![.create, .create, .annihilate, .annihilate]

/-- Boolean compatibility view of `quarticLocalLegKind`. -/
abbrev quarticLocalLegIsCreate : Fin 4 → Bool :=
  ![true, true, false, false]

/-- The free-energy shift of each local quartic leg. -/
abbrev quarticLocalLegEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) : Fin 4 → ℝ :=
  ![ε q.create₁, ε q.create₂, -ε q.annihilate₂, -ε q.annihilate₁]

/-- The total free-energy shift of a quartic vertex. -/
def quarticVertexEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) : ℝ :=
  ε q.create₁ + ε q.create₂ - ε q.annihilate₁ - ε q.annihilate₂

/-- Local quartic-leg operators constructed from arbitrary creation and annihilation maps. -/
abbrev quarticLocalLegOperator
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) : Fin 4 → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  ![create q.create₁, create q.create₂, annihilate q.annihilate₂, annihilate q.annihilate₁]

/-- The fixed ordered quartic vertex operator constructed from arbitrary ladder maps. -/
abbrev quarticVertexOperator
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  (create q.create₁).comp
    ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))

/-- A quartic interaction supported on a specified finite set of vertex labels.

The ambient mode type may be infinite; only the labels in `support` contribute. -/
def quarticInteractionOn (support : Finset (QuarticVertexLabel Mode))
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (g : QuarticVertexLabel Mode → ℂ) : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  ∑ q ∈ support, g q • quarticVertexOperator create annihilate q

/-- The all-label quartic interaction on a finite mode type. -/
def quarticInteraction [Fintype Mode]
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (g : QuarticVertexLabel Mode → ℂ) : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  quarticInteractionOn Finset.univ create annihilate g

end
end Common
end SecondQuantization
