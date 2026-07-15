import LeanCondensedMatter.QuantumTheory.OneParticleSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option linter.style.header false

/-!
# Occupation-number states

Phase 2 of Track D (`notes/roadmaps/second-quantization.md`): the occupation-number
representation of the bosonic Fock basis, `Occupation Mode := Mode →₀ ℕ` — a finitely-supported
function assigning each mode its number of particles. This is the preferred basis for the
bosonic Fock space built in `FockSpace.lean`; symmetric tensor powers are deliberately avoided
as the starting point since the occupation-number picture is simpler and computationally direct.
-/

namespace QuantumTheory

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

/-- **Occupation-number state.** Assigns each mode its (finite) particle number. Since `Mode` is
a `Fintype`, every function `Mode → ℕ` is automatically finitely supported; `Finsupp` is used
regardless since it is the representation the rest of this track (and `Finpartition`-style
combinatorial infrastructure) is built around. -/
def Occupation (Mode : Type*) [Fintype Mode] [DecidableEq Mode] := Mode →₀ ℕ

noncomputable instance : AddCommMonoid (Occupation Mode) :=
  inferInstanceAs (AddCommMonoid (Mode →₀ ℕ))

noncomputable instance : Inhabited (Occupation Mode) := ⟨0⟩

/-- **The vacuum state**: zero particles in every mode. -/
noncomputable def vacuum : Occupation Mode := 0

/-- **The total particle number** of an occupation-number state, `Σᵢ n(i)`. -/
noncomputable def particleNumber (n : Occupation Mode) : ℕ := n.sum fun _ k => k

@[simp]
theorem particleNumber_vacuum : particleNumber (vacuum : Occupation Mode) = 0 :=
  rfl

/-- **The single-particle occupation state** with one particle in mode `i` and none elsewhere. -/
noncomputable def singleOccupation (i : Mode) : Occupation Mode := Finsupp.single i 1

@[simp]
theorem particleNumber_singleOccupation (i : Mode) :
    particleNumber (singleOccupation i : Occupation Mode) = 1 := by
  simp [particleNumber, singleOccupation]

end QuantumTheory
