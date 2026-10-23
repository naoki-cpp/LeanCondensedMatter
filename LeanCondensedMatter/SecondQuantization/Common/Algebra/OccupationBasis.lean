import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

set_option linter.style.header false

/-!
# The occupation-basis interface

`OccupationBasis` captures the statistics-independent structure shared by fermionic and bosonic
occupation descriptions: a vacuum configuration, a per-mode occupation number, its finite support,
vanishing vacuum occupation, and extensionality from the occupation data. These data define the
common total `particleNumber` grading and free occupation energy.

The concrete configuration types remain distinct. Fermions use finite subsets of modes with
occupations in `{0, 1}`, while bosons use finitely supported `ℕ`-valued occupations. Each
statistics-specific algebra supplies its own `OccupationBasis` instance.
-/

namespace SecondQuantization
namespace Common

/-- **The occupation-basis interface**: a Fock-space basis type `Config`, together with a
`vacuum` state and a per-mode occupation-number reading `occupation : Config → Mode → ℕ`, subject
to the physically expected constraints — the vacuum has no particles anywhere, every state has
only finitely many occupied modes, and the reading determines the state. A `class` (not a plain
`structure`) so each statistics' concrete instance is found by typeclass resolution once `Mode`
and its `Config` are fixed, rather than needing to be threaded explicitly. -/
class OccupationBasis (Mode Config : Type*) where
  /-- The zero-particle state. -/
  vacuum : Config
  /-- The occupation number of mode `i` in state `n`. -/
  occupation : Config → Mode → ℕ
  /-- The vacuum has no particles in any mode. -/
  occupation_vacuum : ∀ i, occupation vacuum i = 0
  /-- The finite set of occupied modes. -/
  support : Config → Finset Mode
  /-- A mode is in the support if and only if its occupation is nonzero. -/
  mem_support_iff : ∀ n i, i ∈ support n ↔ occupation n i ≠ 0
  /-- The occupation-number reading determines the state. -/
  ext : ∀ {m n}, (∀ i, occupation m i = occupation n i) → m = n

/-- **The total particle-number grade** of an occupation-basis state. The sum is taken over the support supplied by `OccupationBasis`, so the definition works for
arbitrary mode types without a `Fintype Mode` assumption. -/
noncomputable def particleNumber {Mode Config : Type*} [OccupationBasis Mode Config]
    (n : Config) : ℕ :=
  (OccupationBasis.support (Mode := Mode) (Config := Config) n).sum
    (OccupationBasis.occupation (Mode := Mode) (Config := Config) n)

@[simp]
theorem particleNumber_vacuum {Mode Config : Type*} [OccupationBasis Mode Config] :
    particleNumber (Mode := Mode) (Config := Config)
      (OccupationBasis.vacuum (Mode := Mode) (Config := Config)) = 0 := by
  classical
  simp [particleNumber, OccupationBasis.occupation_vacuum]

/-- Occupation configurations with a sharp total particle number `N`. This grading is
statistics-independent; choosing a canonical Gibbs state is a separate thermal construction. -/
abbrev ParticleNumberSector (Mode Config : Type*) [OccupationBasis Mode Config] (N : ℕ) :=
  {n : Config // particleNumber (Mode := Mode) n = N}

/-- Free energy of a finite-support occupation configuration with one-particle energies `ε`.
The sum is over occupied modes, so `Mode` need not be finite. -/
noncomputable def occupationEnergy {Mode Config : Type*} [OccupationBasis Mode Config]
    (ε : Mode → ℝ) (n : Config) : ℝ :=
  (OccupationBasis.support (Mode := Mode) (Config := Config) n).sum
    (fun i => (OccupationBasis.occupation (Mode := Mode) (Config := Config) n i : ℝ) * ε i)

/-- The vacuum has zero free occupation energy. -/
@[simp]
theorem occupationEnergy_vacuum {Mode Config : Type*} [OccupationBasis Mode Config]
    (ε : Mode → ℝ) :
    occupationEnergy ε
      (OccupationBasis.vacuum (Mode := Mode) (Config := Config)) = 0 := by
  classical
  simp [occupationEnergy, OccupationBasis.occupation_vacuum]

/-- Shifting every free one-particle energy by `-μ` subtracts `μ` times the
occupation number from the many-particle energy. -/
theorem occupationEnergy_sub_const {Mode Config : Type*} [OccupationBasis Mode Config]
    (ε : Mode → ℝ) (μ : ℝ) (n : Config) :
    occupationEnergy (fun i => ε i - μ) n =
      occupationEnergy ε n - μ * (particleNumber (Mode := Mode) n : ℝ) := by
  simp only [occupationEnergy, particleNumber]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_mul, Nat.cast_sum]
  exact mul_comm _ _

/-- Adding a common one-particle energy offset shifts the occupation energy
by that offset times the total particle number. -/
theorem occupationEnergy_add_const {Mode Config : Type*} [OccupationBasis Mode Config]
    (ε : Mode → ℝ) (C : ℝ) (n : Config) :
    occupationEnergy (fun i => ε i + C) n =
      occupationEnergy ε n + C * (particleNumber (Mode := Mode) n : ℝ) := by
  calc
    occupationEnergy (fun i => ε i + C) n =
        occupationEnergy (fun i => ε i - (-C)) n := by
          simp only [sub_neg, neg_neg]
    _ = occupationEnergy ε n - (-C) * (particleNumber (Mode := Mode) n : ℝ) :=
      occupationEnergy_sub_const ε (-C) n
    _ = occupationEnergy ε n + C * (particleNumber (Mode := Mode) n : ℝ) := by
      simp only [neg_mul, sub_neg, neg_neg]


end Common
end SecondQuantization
