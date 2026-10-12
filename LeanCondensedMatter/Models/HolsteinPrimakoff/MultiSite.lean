import LeanCondensedMatter.Models.HolsteinPrimakoff
import LeanCondensedMatter.QuantumTheory.LocalizedSpin
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

set_option linter.style.header false

/-!
# Simultaneous physical occupation sector for Holstein-Primakoff spins

Every site's occupation is bounded by 2s. For finitely many sites, the configuration
Hilbert space is identified linearly with this sector of algebraic bosonic Fock space.
The latter has no completed Hilbert-space structure here; no isometry is asserted.
-/

namespace Models.HolsteinPrimakoff

open SecondQuantization SecondQuantization.Bosonic

noncomputable section
variable {Mode : Type*}

/-- The simultaneous physical sector, imposing n_i <= 2s at every site. -/
def simultaneousSubspace (twiceSpin : ℕ) : Submodule ℂ (FockSpace Mode) :=
  Finsupp.supported ℂ ℂ {n : Occupation Mode | ∀ i, n i ≤ twiceSpin}

private theorem physicalSubspace_eq_supported (twiceSpin : ℕ) (i : Mode) :
    physicalSubspace twiceSpin i =
      Finsupp.supported ℂ ℂ {n : Occupation Mode | n i ≤ twiceSpin} := by
  simpa [physicalSubspace, basisState, Common.basisState] using
    (Finsupp.supported_eq_span_single (R := ℂ) {n : Occupation Mode | n i ≤ twiceSpin}).symm

theorem simultaneousSubspace_eq_iInf (twiceSpin : ℕ) :
    simultaneousSubspace (Mode := Mode) twiceSpin = ⨅ i, physicalSubspace twiceSpin i := by
  have hs : {n : Occupation Mode | ∀ i, n i ≤ twiceSpin} =
      ⋂ i, {n : Occupation Mode | n i ≤ twiceSpin} := by ext n; simp
  unfold simultaneousSubspace
  rw [hs, Finsupp.supported_iInter]
  congr 1
  funext i
  exact (physicalSubspace_eq_supported twiceSpin i).symm

theorem simultaneousSubspace_eq_span (twiceSpin : ℕ) :
    simultaneousSubspace (Mode := Mode) twiceSpin =
      Submodule.span ℂ (basisState '' {n : Occupation Mode | ∀ i, n i ≤ twiceSpin}) := by
  simpa [simultaneousSubspace, basisState, Common.basisState] using
    (Finsupp.supported_eq_span_single (R := ℂ) {n : Occupation Mode | ∀ i, n i ≤ twiceSpin})

section FiniteSites
variable [Fintype Mode]

/-- Convert finite spin configurations to bounded bosonic occupations and back. -/
def configurationEquivOccupation (twiceSpin : ℕ) :
    QuantumTheory.LocalizedSpin.Configuration twiceSpin Mode ≃
      {n : Occupation Mode // ∀ i, n i ≤ twiceSpin} where
  toFun c := ⟨Finsupp.equivFunOnFinite.symm (fun i => (c i).val), fun i => by
    simpa using Nat.le_of_lt_succ (c i).isLt⟩
  invFun n i := ⟨n.val i, Nat.lt_succ_of_le (n.property i)⟩
  left_inv c := by funext i; apply Fin.ext; simp
  right_inv n := by apply Subtype.ext; ext i; simp

/-- A basis-preserving complex-linear equivalence from the full finite-spin state
space to the simultaneous physical Fock sector. This is an algebraic identification. -/
def spinStateEquiv (twiceSpin : ℕ) :
    QuantumTheory.LocalizedSpin.State twiceSpin Mode ≃ₗ[ℂ]
      simultaneousSubspace (Mode := Mode) twiceSpin :=
  (WithLp.linearEquiv 2 ℂ (QuantumTheory.LocalizedSpin.Configuration twiceSpin Mode → ℂ)).trans
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ _).symm.trans
      ((Finsupp.domLCongr (configurationEquivOccupation twiceSpin)).trans
        (Finsupp.supportedEquivFinsupp
          {n : Occupation Mode | ∀ i, n i ≤ twiceSpin}).symm))

theorem spinStateEquiv_single (twiceSpin : ℕ)
    (c : QuantumTheory.LocalizedSpin.Configuration twiceSpin Mode) :
    (spinStateEquiv twiceSpin (EuclideanSpace.single c 1) : FockSpace Mode) =
      basisState (configurationEquivOccupation twiceSpin c).val := by
  classical
  simp [spinStateEquiv, EuclideanSpace.single, PiLp.single,
    Finsupp.linearEquivFunOnFinite_symm_single, Finsupp.domLCongr_single,
    basisState, Common.basisState]

end FiniteSites

end
end Models.HolsteinPrimakoff
