import LeanCondensedMatter.QuantumTheory.SpinHalf
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite collections of localized spin-1/2 degrees of freedom

States are complex amplitudes on all spin configurations. The labels `0` and `1`
denote up and down along the chosen Cartesian z axis. Site exchange is a unitary
involution. The one-spin-deviation embedding is isometric, including arbitrary
complex superpositions. No free-boson approximation enters this representation.
-/

namespace QuantumTheory.SpinHalf

open scoped BigOperators InnerProductSpace

noncomputable section

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- A localized spin-1/2 configuration, with `0` up and `1` down. -/
abbrev Configuration (Site : Type*) := Site → Fin 2

/-- The full finite-spin Hilbert space. -/
abbrev State (Site : Type*) [Fintype Site] := EuclideanSpace ℂ (Configuration Site)

/-- The action of a two-level matrix at a single site. -/
def atSite (A : InternalSpace.PauliMatrix) (i : Site) : State Site →ₗ[ℂ] State Site where
  toFun ψ := WithLp.toLp 2 fun c => ∑ s : Fin 2, A (c i) s * ψ (Function.update c i s)
  map_add' ψ φ := by ext c; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a ψ := by ext c; simp [Finset.mul_sum]; ring

/-- Exchange the spin labels at two sites. -/
def exchangeConfiguration (i j : Site) : Equiv.Perm (Configuration Site) where
  toFun c := c ∘ Equiv.swap i j
  invFun c := c ∘ Equiv.swap i j
  left_inv c := by ext k; simp
  right_inv c := by ext k; simp

/-- Unitary exchange of two localized spins. -/
def exchange (i j : Site) : State Site ≃ₗᵢ[ℂ] State Site :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (exchangeConfiguration i j)

theorem exchange_apply (i j : Site) (ψ : State Site) (c : Configuration Site) :
    exchange i j ψ c = ψ (c ∘ Equiv.swap i j) := rfl

theorem exchange_involutive (i j : Site) : Function.Involutive (exchange i j) := by
  intro ψ
  ext c
  simp only [exchange_apply]
  apply congrArg ψ
  funext k
  simp

theorem exchange_isSymmetric (i j : Site) : (exchange i j).toLinearMap.IsSymmetric := by
  intro ψ φ
  change inner ℂ (exchange i j ψ) φ = inner ℂ ψ (exchange i j φ)
  simpa only [exchange_involutive i j φ] using
    (exchange i j).inner_map_map ψ (exchange i j φ)

theorem id_sub_exchange_isPositive (i j : Site) :
    (LinearMap.id - (exchange i j).toLinearMap).IsPositive := by
  refine ⟨LinearMap.IsSymmetric.id.sub (exchange_isSymmetric i j), fun ψ => ?_⟩
  have h := re_inner_le_norm (𝕜 := ℂ) (exchange i j ψ) ψ
  rw [(exchange i j).norm_map] at h
  change 0 ≤ RCLike.re (inner ℂ (ψ - exchange i j ψ) ψ)
  simp only [inner_sub_left, map_sub, inner_self_eq_norm_sq]
  nlinarith

/-- Dimensionful Cartesian spin product at two sites. -/
def spinDot (hbar : ℝ) (i j : Site) : State Site →ₗ[ℂ] State Site :=
  ((hbar / 2 : ℝ) : ℂ) ^ 2 •
    ((atSite InternalSpace.pauliX i).comp (atSite InternalSpace.pauliX j) +
     (atSite InternalSpace.pauliY i).comp (atSite InternalSpace.pauliY j) +
     (atSite InternalSpace.pauliZ i).comp (atSite InternalSpace.pauliZ j))

/-- Spin-1/2 exchange identity, with the same Pauli convention as `spinMatrix`.
Stancil-Prabhakar, Section 2.4, equations (2.63)-(2.70). -/
theorem spinDot_eq_exchange (hbar : ℝ) (i j : Site) (hij : i ≠ j) :
    spinDot hbar i j = ((hbar : ℂ) ^ 2 / 4) •
      (2 • (exchange i j).toLinearMap - LinearMap.id) := by
  ext ψ c
  have hswap : c ∘ Equiv.swap i j = Function.update (Function.update c j (c i)) i (c j) :=
    Equiv.comp_swap_eq_update i j c
  have hui := Function.update_eq_self i c
  have huj := Function.update_eq_self j c
  generalize hci : c i = si
  generalize hcj : c j = sj
  fin_cases si <;> fin_cases sj <;> simp only [hci, hcj] at hui huj hswap <;>
    simp [spinDot, atSite, exchange_apply, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ, Fin.sum_univ_two, hij, hij.symm, hci, hcj,
      hswap, Function.update_comm hij, hui, huj] <;> ring

/-- A normalized fully polarized state. -/
def polarized : State Site := EuclideanSpace.single (fun _ => 0) 1

theorem norm_polarized : ‖polarized (Site := Site)‖ = 1 := by simp [polarized]

theorem exchange_polarized (i j : Site) : exchange i j polarized = polarized := by
  change LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ _ (EuclideanSpace.single _ _) = _
  rw [LinearIsometryEquiv.piLpCongrLeft_single]
  rfl

/-- The configuration with just site `i` reversed from the polarized reference. -/
def oneDown (i : Site) : Configuration Site := Pi.single i 1

theorem oneDown_injective : Function.Injective (oneDown (Site := Site)) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [oneDown, Pi.single_apply, hij] at this

/-- A localized one-spin-deviation basis state. -/
def oneMagnonKet (i : Site) : State Site := EuclideanSpace.single (oneDown i) 1

theorem exchange_oneMagnonKet (i j k : Site) :
    exchange i j (oneMagnonKet k) = oneMagnonKet (Equiv.swap i j k) := by
  change LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ _ (EuclideanSpace.single _ _) = _
  rw [LinearIsometryEquiv.piLpCongrLeft_single]
  congr 1
  ext l
  simp [exchangeConfiguration, oneDown, Pi.single_apply, Equiv.swap_apply_eq_iff]

private def oneMagnonLinear : EuclideanSpace ℂ Site →ₗ[ℂ] State Site where
  toFun ψ := ∑ i, ψ i • oneMagnonKet i
  map_add' ψ φ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a ψ := by simp [Finset.smul_sum, smul_smul]

/-- The isometric embedding of one-spin-deviation amplitudes into the full spin space. -/
def oneMagnonEmbedding : EuclideanSpace ℂ Site →ₗᵢ[ℂ] State Site :=
  oneMagnonLinear.isometryOfInner fun ψ φ => by
    simp [oneMagnonLinear, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      oneMagnonKet, EuclideanSpace.inner_single_left, PiLp.single_apply,
      oneDown_injective.eq_iff, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem oneMagnonEmbedding_apply (ψ : EuclideanSpace ℂ Site) :
    oneMagnonEmbedding ψ = ∑ i, ψ i • oneMagnonKet i := rfl

end
end QuantumTheory.SpinHalf
