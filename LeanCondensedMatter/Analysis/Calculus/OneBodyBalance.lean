import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct

set_option linter.style.header false

/-!
# Algebraic symmetric-localization balance identity

This module contains one particular algebraic realization of a localized one-body balance. For a
one-body quantity `m` and a supplied localization map `M`, define

```text
ρₘ(f) = 1/2 {M f, m}.
```

Its commutator with `h` splits as

```text
[h, ρₘ(f)]
  = 1/2 {[h, M f], m}
  + 1/2 {M f, [h, m]}.
```

The symmetrized-product algebra itself lives in `Analysis.Operator.SymmetrizedProduct`.  This file
should be read as a symmetric-localization realization, not as the definition of a general balance
law; the representation-independent `δ(Q f) = J(d f) + S(f)` interface lives in
`Analysis.Calculus.BalanceLaw`.
-/

namespace ConservationLaw

variable {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- A one-body quantity localized by the observable `M f`. -/
noncomputable def localizedQuantity (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) : V →ₗ[ℂ] V :=
  symmetrizedProduct (M f) m

/-- When localization commutes with the quantity, symmetric localization reduces to `M f ∘ m`. -/
theorem localizedQuantity_eq_comp_of_commutes
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test)
    (hcomm : linearCommutator (M f) m = 0) :
    localizedQuantity V M m f = (M f).comp m := by
  simpa [localizedQuantity] using
    (symmetrizedProduct_eq_comp_of_commutes (M f) m hcomm)

/-- Charge-like quantities `q I` commute with localization and reduce to scalar multiplication. -/
@[simp]
theorem localizedQuantity_smul_id
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    localizedQuantity V M (q • LinearMap.id) f = q • M f := by
  simp [localizedQuantity]

/-- Canonical transport part of the symmetric-localization commutator identity. -/
noncomputable def transportCommutator (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test) :
    V →ₗ[ℂ] V :=
  symmetrizedProduct (linearCommutator h (M f)) m

/-- For a charge-like quantity `q I`, the canonical transport term is `q [h, M f]`. -/
@[simp]
theorem transportCommutator_smul_id (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    transportCommutator V h M (q • LinearMap.id) f =
      q • linearCommutator h (M f) := by
  simp [transportCommutator]

/-- Canonical source/torque part of the symmetric-localization commutator identity. -/
noncomputable def sourceCommutator (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test) :
    V →ₗ[ℂ] V :=
  symmetrizedProduct (M f) (linearCommutator h m)

/-- A conserved quantity has no local source/torque contribution. -/
@[simp]
theorem sourceCommutator_eq_zero_of_commutes (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test)
    (hm : linearCommutator h m = 0) :
    sourceCommutator V h M m f = 0 := by
  simp [sourceCommutator, hm]

/-- Charge-like quantities `q I` have no source/torque term. -/
theorem sourceCommutator_smul_id (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) (f : Test) :
    sourceCommutator V h M (q • LinearMap.id) f = 0 := by
  apply sourceCommutator_eq_zero_of_commutes V h M (q • LinearMap.id) f
  exact linearCommutator_smul_id_right h q

/-- Purely algebraic balance decomposition for the symmetric localization of a one-body quantity. -/
theorem linearCommutator_localizedQuantity (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test) :
    linearCommutator h (localizedQuantity V M m f) =
      transportCommutator V h M m f + sourceCommutator V h M m f := by
  simpa [localizedQuantity, transportCommutator, sourceCommutator] using
    linearCommutator_symmetrizedProduct h (M f) m

/-- For a conserved quantity, the localized balance identity contains only the transport term. -/
theorem linearCommutator_localizedQuantity_of_commutes (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (m : V →ₗ[ℂ] V) (f : Test)
    (hm : linearCommutator h m = 0) :
    linearCommutator h (localizedQuantity V M m f) =
      transportCommutator V h M m f := by
  rw [linearCommutator_localizedQuantity]
  simp [sourceCommutator, hm]

end ConservationLaw
