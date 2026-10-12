import Mathlib
import LeanCondensedMatter.SecondQuantization.Common.Algebra.SupportShift
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Statistics-independent quartic interaction structure

A number-conserving quartic interaction vertex carries two creation modes and two annihilation modes.
The local-leg ordering, generic ladder-map operator constructors, finite vertex-sequence products,
finite-support interaction sums, and free-energy shifts are independent of particle statistics and
imaginary-time evolution.

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

/-- One local leg of a quartic vertex, carrying both its ladder kind and mode. -/
inductive QuarticLocalLeg (Mode : Type*) where
  | create (mode : Mode)
  | annihilate (mode : Mode)
  deriving DecidableEq

namespace QuarticLocalLeg

/-- The signed free-energy shift carried by a quartic local leg. -/
@[simp]
def energyShift (ε : Mode → ℝ) : QuarticLocalLeg Mode → ℝ
  | .create i => ε i
  | .annihilate i => -ε i

/-- Realize a quartic local leg using arbitrary creation and annihilation maps. -/
@[simp]
def operator (leg : QuarticLocalLeg Mode)
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  match leg with
  | .create i => create i
  | .annihilate i => annihilate i

end QuarticLocalLeg

/-- The four semantic local legs of a quartic vertex, in fixed operator-composition order. -/
abbrev quarticLocalLeg (q : QuarticVertexLabel Mode) : Fin 4 → QuarticLocalLeg Mode :=
  ![.create q.create₁, .create q.create₂, .annihilate q.annihilate₂, .annihilate q.annihilate₁]

/-- The free-energy shift of each local quartic leg. -/
abbrev quarticLocalLegEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) (l : Fin 4) : ℝ :=
  (quarticLocalLeg q l).energyShift ε

/-- The total free-energy shift of a quartic vertex. -/
def quarticVertexEnergyShift (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) : ℝ :=
  ε q.create₁ + ε q.create₂ - ε q.annihilate₁ - ε q.annihilate₂

/-- Local quartic-leg operators constructed from arbitrary creation and annihilation maps. -/
abbrev quarticLocalLegOperator
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) (l : Fin 4) : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  (quarticLocalLeg q l).operator create annihilate

/-- The fixed ordered quartic vertex operator constructed from arbitrary ladder maps. -/
abbrev quarticVertexOperator
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : QuarticVertexLabel Mode) : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  (create q.create₁).comp
    ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))

/-- Ordered product of a finite sequence of quartic vertex operators. -/
noncomputable def quarticVertexSequenceOperator {n : ℕ}
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : Fin n → QuarticVertexLabel Mode) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  (List.ofFn fun i => quarticVertexOperator create annihilate (q i)).prod

/-- Prepending one quartic vertex prepends its operator by composition. -/
@[simp]
theorem quarticVertexSequenceOperator_cons {n : ℕ}
    (create annihilate : Mode → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q0 : QuarticVertexLabel Mode) (q : Fin n → QuarticVertexLabel Mode) :
    quarticVertexSequenceOperator create annihilate (Fin.cons q0 q) =
      (quarticVertexOperator create annihilate q0).comp
        (quarticVertexSequenceOperator create annihilate q) := by
  simp [quarticVertexSequenceOperator, Module.End.mul_eq_comp]

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
variable {Mode Config : Type*}

/-- Two creation and two annihilation maps with opposite fixed charges preserve the grading.
This uses only support shifts, not CAR/CCR or a finite configuration type. -/
theorem carriesShift_quarticVertexOperator {G : Type*} [AddCommGroup G]
    (grading : Config 竊・G) (charge : G)
    (create annihilate : Mode 竊・AlgebraicFock Config 竊停ｗ[邃・ AlgebraicFock Config)
    (hcreate : 竏 i, CarriesShift grading (create i) charge)
    (hannihilate : 竏 i, CarriesShift grading (annihilate i) (-charge))
    (q : QuarticVertexLabel Mode) :
    CarriesShift grading (quarticVertexOperator create annihilate q) 0 := by
  have h := (hcreate q.create竄・.comp
    ((hcreate q.create竄・.comp ((hannihilate q.annihilate竄・.comp
      (hannihilate q.annihilate竄・))
  have hcharge : charge + (charge + (-charge + -charge)) = 0 := by abel
  simpa only [quarticVertexOperator, hcharge] using h

/-- A finite-support sum of neutral quartic vertices preserves the same grading. -/
theorem carriesShift_quarticInteractionOn {G : Type*} [AddCommGroup G]
    (grading : Config 竊・G) (charge : G)
    (create annihilate : Mode 竊・AlgebraicFock Config 竊停ｗ[邃・ AlgebraicFock Config)
    (hcreate : 竏 i, CarriesShift grading (create i) charge)
    (hannihilate : 竏 i, CarriesShift grading (annihilate i) (-charge))
    (support : Finset (QuarticVertexLabel Mode)) (g : QuarticVertexLabel Mode 竊・邃・ :
    CarriesShift grading (quarticInteractionOn support create annihilate g) 0 := by
  apply CarriesShift.sum
  intro q _
  exact (carriesShift_quarticVertexOperator grading charge create annihilate
    hcreate hannihilate q).smul (g q)

end Common
end SecondQuantization
