# Finite response and conductivity evaluation

The finite-table API is the calculation-facing boundary between proved operator-level linear
response and concrete small-model algebra.

## Generic response workflow

For a finite spectral index `ι`, provide

```text
Eₙ, pₙ, Aₘₙ, Bₘₙ
```

as a `QuantumTheory.LinearResponse.FiniteLehmannTable ι`.  Bundle the table with `ℏ`, driving
frequency `ω`, and retained switching/broadening rate `η` in
`QuantumTheory.LinearResponse.FiniteResponseProblem ι`, then evaluate with
`FiniteResponseProblem.value`.

This path is appropriate for arbitrary measured/source observables.  In particular, a later spin
response can use a spin-current matrix table for `A` and a charge-current matrix table for `B`
without changing the Kubo derivation.

If an operator-level finite pure-point model is already available, use
`finiteResponseProblemOfPurePoint`.  The theorem
`finiteResponseProblemOfPurePoint_value` states that the scalar evaluation is exactly the existing
`purePointLehmannSeries`.

## Electrical conductivity workflow

Electrical conductivity additionally needs the Peierls/contact expectation and physical volume.
Provide the current-current spectral data plus contact value as a
`SecondQuantization.Fermionic.Transport.FiniteConductivityTable ι`, then bundle

```text
table, volume, ℏ, ω, η
```

in `SecondQuantization.Fermionic.Transport.FiniteConductivityProblem ι`.  Evaluate it with
`FiniteConductivityProblem.value`.

For a proved finite pure-point hopping model, `finiteDirectionalConductivityProblemOfPurePoint`
constructs the full input from the existing Peierls current/contact data.  The theorem
`finiteDirectionalConductivityProblemOfPurePoint_value` identifies the result exactly with
`finiteKuboGreenwoodDirectionalConductivity`.

The intended vertical path is therefore

```text
model operators H, A, B (or H, J, C)
  -> proved finite spectral data
  -> FiniteLehmannTable / FiniteConductivityTable
  -> FiniteResponseProblem / FiniteConductivityProblem
  -> exact scalar value
```

The two-site dimer validation is the first electrical example: its operator-derived energies,
current matrix elements, and contact expectation feed the finite conductivity table, which evaluates
exactly to `1/5` at `ℏ = 1`, `ω = 0`, `η = 1`, and unit volume.

## Exact versus numerical layers

The public boundary above remains in theorem-level `ℝ` and `ℂ`.  It contains no `Float`, numerical
diagonalizer, tolerance, or uncontrolled approximation.  A future numerical/export layer should
consume finite tables downstream and state explicitly how machine values approximate the exact
inputs or outputs.  Numerical convenience must not replace the theorem equating the table evaluator
with the operator-level Kubo/Lehmann result.

Likewise, fixed positive `η` and finite physical volume are explicit inputs.  This workflow does not
silently take a zero-broadening/DC or thermodynamic limit.
