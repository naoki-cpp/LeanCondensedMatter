import LeanCondensedMatter.Combinatorics.Cumulant.Inversion

set_option linter.style.header false

/-!
# Normalized finite-set functions and moment–cumulant equivalence

A normalized finite-set function takes the value `1` on the empty set. On this natural domain the
moment and cumulant transforms are genuine mutually inverse endomorphisms, so public users do not
need to carry a nonemptiness side condition at every evaluation.
-/

namespace Combinatorics

/-- A finite-set function normalized to `1` on the empty set. -/
structure NormalizedSetFunction (α R : Type*) [One R] where
  /-- The underlying function on finite subsets. -/
  toFun : Finset α → R
  map_empty : toFun ∅ = 1

instance [One R] : CoeFun (NormalizedSetFunction α R) (fun _ => Finset α → R) :=
  ⟨NormalizedSetFunction.toFun⟩

@[ext]
theorem NormalizedSetFunction.ext [One R]
    {f g : NormalizedSetFunction α R} (h : ∀ S, f S = g S) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  funext S
  exact h S

namespace NormalizedSetFunction

variable {α R : Type*} [DecidableEq α] [CommRing R]

private theorem momentFromCumulant_empty (κ : Finset α → R) :
    Finpartition.momentFromCumulant κ ∅ = 1 := by
  classical
  rw [Finpartition.momentFromCumulant, Fintype.sum_unique]
  have hparts : (default : Finpartition (∅ : Finset α)).parts = ∅ := by simp
  simp [Finpartition.partitionProduct, hparts]

private theorem cumulantFromMoment_empty (m : Finset α → R) :
    Finpartition.cumulantFromMoment m ∅ = 1 := by
  classical
  rw [Finpartition.cumulantFromMoment, Fintype.sum_unique]
  have hdefault_top : (default : Finpartition (∅ : Finset α)) = ⊤ :=
    Subsingleton.elim _ _
  have hparts_top : (⊤ : Finpartition (∅ : Finset α)).parts = ∅ := by simp
  rw [hdefault_top]
  simp [Finpartition.partitionProduct, hparts_top]

/-- Moment transform on normalized finite-set functions. -/
noncomputable def moment (κ : NormalizedSetFunction α R) : NormalizedSetFunction α R where
  toFun := Finpartition.momentFromCumulant κ
  map_empty := momentFromCumulant_empty κ

/-- Cumulant transform on normalized finite-set functions. -/
noncomputable def cumulant (m : NormalizedSetFunction α R) : NormalizedSetFunction α R where
  toFun := Finpartition.cumulantFromMoment m
  map_empty := cumulantFromMoment_empty m

@[simp]
theorem moment_apply (κ : NormalizedSetFunction α R) (S : Finset α) :
    κ.moment S = Finpartition.momentFromCumulant κ S :=
  rfl

@[simp]
theorem cumulant_apply (m : NormalizedSetFunction α R) (S : Finset α) :
    m.cumulant S = Finpartition.cumulantFromMoment m S :=
  rfl

/-- Cumulant after moment is the identity on normalized finite-set functions. -/
theorem cumulant_moment (κ : NormalizedSetFunction α R) : κ.moment.cumulant = κ := by
  ext S
  by_cases hS : S = ∅
  · subst S
    rw [κ.moment.cumulant.map_empty, κ.map_empty]
  · exact Finpartition.cumulantFromMoment_momentFromCumulant κ hS

/-- Moment after cumulant is the identity on normalized finite-set functions. -/
theorem moment_cumulant (m : NormalizedSetFunction α R) : m.cumulant.moment = m := by
  ext S
  by_cases hS : S = ∅
  · subst S
    rw [m.cumulant.moment.map_empty, m.map_empty]
  · exact Finpartition.momentFromCumulant_cumulantFromMoment m hS

/-- Moment and cumulant coordinates are equivalent on normalized finite-set functions. -/
noncomputable def momentCumulantEquiv :
    NormalizedSetFunction α R ≃ NormalizedSetFunction α R where
  toFun := moment
  invFun := cumulant
  left_inv := cumulant_moment
  right_inv := moment_cumulant

end NormalizedSetFunction
end Combinatorics
