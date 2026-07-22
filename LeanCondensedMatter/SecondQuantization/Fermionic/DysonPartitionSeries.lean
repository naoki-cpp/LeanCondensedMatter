import LeanCondensedMatter.SecondQuantization.Fermionic.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.FreeBoltzmannWeight
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.FormalLogPartitionFunction

set_option linter.style.header false

/-!
# The Dyson-coefficient partition-function series

Step 5 (PR 5) of Phase 9's Dyson-series plan (`notes/roadmaps/second-quantization.md`): packages
`dysonCoeff`'s traces into a genuine `PowerSeries ℂ` in the perturbation parameter `λ`, and
connects it to `FormalLogPartitionFunction.lean`'s existing `normalizePartitionSeries`/
`formalLogPartitionFunction` layer — the same combinatorial `log Z` groundwork that layer already
supports for an *arbitrary* partition-function series, now with a concrete (if still not
convergence-checked) candidate series to feed it.

`dysonPartitionCoeff ε β V n := Tr[e^{-βH₀} Dₙ(β)]` is the `n`-th order trace of the Dyson
coefficient against the free Gibbs weight — the `λⁿ`-coefficient a genuine perturbative partition
function `Z(λ) = Tr[e^{-β(H₀+λV)}]` would have, *if* the (not established here) equality
`Σₙ λⁿ Dₙ(β) = e^{βH₀} e^{-β(H₀+λV)}` held as a genuine (rather than merely formal) operator
series — the solution, at `τ := β`, of `dU_I/dτ = -λ V_I(τ) U_I(τ)`, `U_I(0) = 1`, the ODE
`dysonCoeff`'s left-multiplying recursion represents (`V_I(τ) := e^{τH₀} V e^{-τH₀}` acts from the
left in `Dₙ₊₁(τ) = -∫ V_I(σ) ∘ Dₙ(σ) dσ`, so its solution `U_I` satisfies `e^{-βH₀} U_I(β) =
e^{-β(H₀+λV)}`, matching `dysonPartitionCoeff`'s own `e^{-βH₀} ∘ Dₙ(β)` shape exactly).
`dysonPartitionSeries` assembles these coefficients into a `PowerSeries ℂ`; no claim about
its radius of convergence, or about matching a genuine analytic partition function beyond the
`n = 0` term, is made.
-/

namespace SecondQuantization

open PowerSeries

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The `n`-th order Dyson partition-function coefficient**, `Tr[e^{-βH₀} Dₙ(β)]`. -/
noncomputable def dysonPartitionCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) : ℂ :=
  traceFock ((imaginaryTimeEvolveFree ε (-β)).comp (dysonCoeff ε V n β))

/-- **The Dyson partition-function series**, `Σₙ dysonPartitionCoeff(n) λⁿ` — packaging
`dysonPartitionCoeff` into a genuine `PowerSeries ℂ` in the perturbation parameter, with no
convergence claim. -/
noncomputable def dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : PowerSeries ℂ :=
  PowerSeries.mk (dysonPartitionCoeff ε β V)

omit [LinearOrder Mode] in
theorem coeff_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    PowerSeries.coeff n (dysonPartitionSeries ε β V) = dysonPartitionCoeff ε β V n :=
  PowerSeries.coeff_mk n _

omit [LinearOrder Mode] in
/-- **The `n = 0` term of `dysonPartitionSeries` is the free partition function**: `D₀(β) = id`, so
`Tr[e^{-βH₀} D₀(β)] = Tr[e^{-βH₀}] = Z₀(β)` — the physically expected zeroth-order (unperturbed)
term of a perturbative partition function series, and exactly the normalization
`normalizePartitionSeries` needs to be nonzero to apply `formalLogPartitionFunction`. -/
theorem constantCoeff_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.constantCoeff (dysonPartitionSeries ε β V) = freePartitionFunction ε β := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_dysonPartitionSeries, dysonPartitionCoeff,
    dysonCoeff_zero, LinearMap.comp_id]
  change Common.traceFock (imaginaryTimeEvolveFree ε (-β)) = freePartitionFunction ε β
  rw [imaginaryTimeEvolveFree, Common.traceFock_diagonalEvolution_eq_weightSum]
  congr 1
  funext n
  rw [Common.boltzmannWeight, freeBoltzmannWeight]
  push_cast [fermionEnergy]
  ring_nf

omit [LinearOrder Mode] in
@[simp]
theorem dysonPartitionCoeff_zero (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    dysonPartitionCoeff ε β V 0 = freePartitionFunction ε β := by
  rw [← coeff_dysonPartitionSeries, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_dysonPartitionSeries]

/-- **The normalized/log'd Dyson partition series**, feeding `dysonPartitionSeries` into the
existing `FormalLogPartitionFunction.lean` layer once its zeroth-order term is known nonzero
(`freePartitionFunction_ne_zero`). -/
noncomputable def dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : PowerSeries ℂ :=
  formalLogPartitionFunction (normalizePartitionSeries (dysonPartitionSeries ε β V))

omit [LinearOrder Mode] in
theorem constantCoeff_normalizePartitionSeries_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.constantCoeff (normalizePartitionSeries (dysonPartitionSeries ε β V)) = 1 :=
  constantCoeff_normalizePartitionSeries
    (constantCoeff_dysonPartitionSeries ε β V ▸ freePartitionFunction_ne_zero ε β)

omit [LinearOrder Mode] in
/-- **`dysonFormalLogPartitionFunction` has vanishing constant term**, inherited from
`constantCoeff_formalLogPartitionFunction` via the nonvanishing zeroth-order Dyson coefficient
(`constantCoeff_dysonPartitionSeries`/`freePartitionFunction_ne_zero`). -/
theorem constantCoeff_dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.constantCoeff (dysonFormalLogPartitionFunction ε β V) = 0 :=
  constantCoeff_formalLogPartitionFunction
    (constantCoeff_normalizePartitionSeries_dysonPartitionSeries ε β V)

end SecondQuantization
