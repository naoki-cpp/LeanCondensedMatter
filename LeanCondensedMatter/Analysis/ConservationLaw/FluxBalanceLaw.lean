import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Flux balance laws and current representations

A representation-independent local balance is an equality of linear maps
`δ.comp Q = Φ + S`, with `Function.FactorsThrough Φ d`. Here `d : Test →ₗ[𝕜] OneForm`
is the differential test map; no full current extension is part of the balance data.

A differential current is a chosen linear map `J` satisfying `Φ = J.comp d`.
A local current-density representation additionally chooses a density `j` with
`Φ = (pairing j).comp d`, where the bilinear pairing is supplied by the model.
Both representations are subtype fibers, not alternative balance-law structures.
Factorization alone makes no claim of locality or uniqueness.

Currents agreeing on exact differential data may differ by an invisible extension
`K.comp d = 0`, in the kernel of `(LinearMap.llcomp 𝕜 Test OneForm Obs).flip d`.
The existing `LinearMap.sub_comp` and `LinearMap.sub_mem_ker_iff` express this ambiguity;
injectivity of the paired differential-test map gives density uniqueness.

The word *flux* refers to a balance term, not an intrinsic Berry-curvature
or disorder-independent transport mechanism.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

/-- Representation-independent local balance data.

`transport` is defined on test objects themselves and is required only to depend on their
differentials.  A full `OneForm → Obs` current is deliberately not part of this structure. -/
structure FluxBalanceLaw
    (δ : Obs →ₗ[𝕜] Obs)
    (Q : Test →ₗ[𝕜] Obs)
    (d : Test →ₗ[𝕜] OneForm) where
  /-- Flux defined on test data, without choosing a full one-form current. -/
  transport : Test →ₗ[𝕜] Obs
  /-- Transport is insensitive to changes of a test object that leave its differential fixed. -/
  transport_depends : Function.FactorsThrough transport d
  /-- Local source, sink, or torque functional. -/
  source : Test →ₗ[𝕜] Obs
  /-- The local balance identity as an equality of linear maps on tests. -/
  balance : δ.comp Q = transport + source

namespace FluxBalanceLaw

/-- If the differential test vanishes, only the source can change the localized quantity. -/
theorem evolution_eq_source_of_differential_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d) {f : Test} (hf : d f = 0) :
    δ (Q f) = B.source f := by
  have hz : B.transport f = 0 := by
    calc
      B.transport f = B.transport 0 :=
        B.transport_depends (by simpa only [map_zero] using hf)
      _ = 0 := map_zero B.transport
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, hz, zero_add] using
    congrArg (fun L : Test →ₗ[𝕜] Obs => L f) B.balance

/-- A test object in the kernel of `d` gives a conserved quantity when its source also vanishes. -/
theorem evolution_eq_zero_of_differential_eq_zero_of_source_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d) {f : Test}
    (hf : d f = 0) (hsource : B.source f = 0) :
    δ (Q f) = 0 := by
  rw [B.evolution_eq_source_of_differential_eq_zero hf, hsource]

/-- Source-free transport flux is unique for fixed evolution, localized quantity, and differential. -/
theorem sourceFreeFlux_unique
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B₁ B₂ : FluxBalanceLaw δ Q d)
    (hsource₁ : B₁.source = 0) (hsource₂ : B₂.source = 0) (f : Test) :
    B₁.transport f = B₂.transport f := by
  have h₁ : δ.comp Q = B₁.transport := by
    simpa only [hsource₁, add_zero] using B₁.balance
  have h₂ : δ.comp Q = B₂.transport := by
    simpa only [hsource₂, add_zero] using B₂.balance
  exact congrArg (fun L : Test →ₗ[𝕜] Obs => L f) (h₁.symm.trans h₂)

/-- Scaling the evolution scales representation-independent transport and source. -/
noncomputable def scaleEvolution
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d) (c : 𝕜) :
    FluxBalanceLaw (c • δ) Q d where
  transport := c • B.transport
  transport_depends := B.transport_depends.comp_left (fun y : Obs => c • y)
  source := c • B.source
  balance := by rw [LinearMap.smul_comp, B.balance, smul_add]

section TransportSourceAmbiguity

variable {R T F O : Type*} [CommRing R]
variable [AddCommMonoid T] [Module R T]
variable [AddCommMonoid F] [Module R F]
variable [AddCommMonoid O] [Module R O]

/-- Redistribute a differential-dependent functional from source to transport without changing
the localized evolution. A shift of a full current by `J` is the special case
`K = J.comp d`; no full current extension is required. -/
noncomputable def shiftTransportSource
    {δ : O →ₗ[R] O} {Q : T →ₗ[R] O} {d : T →ₗ[R] F}
    (B : FluxBalanceLaw δ Q d) (K : T →ₗ[R] O)
    (hK : Function.FactorsThrough K d) : FluxBalanceLaw δ Q d where
  transport := B.transport + K
  transport_depends := by
    intro f g hfg
    simp only [LinearMap.add_apply]
    rw [B.transport_depends hfg, hK hfg]
  source := B.source + (-1 : R) • K
  balance := by
    rw [B.balance]
    module

@[simp]
theorem shiftTransportSource_transport
    {δ : O →ₗ[R] O} {Q : T →ₗ[R] O} {d : T →ₗ[R] F}
    (B : FluxBalanceLaw δ Q d) (K : T →ₗ[R] O)
    (hK : Function.FactorsThrough K d) :
    (B.shiftTransportSource K hK).transport = B.transport + K :=
  rfl

@[simp]
theorem shiftTransportSource_source
    {δ : O →ₗ[R] O} {Q : T →ₗ[R] O} {d : T →ₗ[R] F}
    (B : FluxBalanceLaw δ Q d) (K : T →ₗ[R] O)
    (hK : Function.FactorsThrough K d) :
    (B.shiftTransportSource K hK).source = B.source + (-1 : R) • K :=
  rfl

end TransportSourceAmbiguity

/-- If the source itself depends only on differential data, it may be absorbed into transport.
The resulting law is source-free without choosing any full current functional. -/
noncomputable def absorbSource
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d)
    (hsource : Function.FactorsThrough B.source d) :
    FluxBalanceLaw δ Q d where
  transport := B.transport + B.source
  transport_depends := by
    intro f g hfg
    simp only [LinearMap.add_apply]
    rw [B.transport_depends hfg, hsource hfg]
  source := 0
  balance := by simpa only [add_zero] using B.balance

end FluxBalanceLaw

section CurrentRepresentation

variable {CurrentDensity : Type*}
variable [AddCommMonoid CurrentDensity] [Module 𝕜 CurrentDensity]

/-- Data of one chosen flux functional representing `Φ` through `d`.

No locality or uniqueness claim is bundled into this structure. -/
abbrev DifferentialCurrentRepresentation
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) :=
  {J : OneForm →ₗ[𝕜] Obs // Φ = J.comp d}

/-- A bilinear pairing of a current density with 1-form-like test data.

Concrete models are responsible for showing that this supplied pairing has the intended local or
zeroth-order meaning. -/
abbrev LocalCurrentPairing :=
  CurrentDensity →ₗ[𝕜] (OneForm →ₗ[𝕜] Obs)

/-- A transport functional has a local current-density representation relative to a supplied
pairing when one density `j` represents `Φ` through `d`. -/
abbrev LocalCurrentDensityRepresentation
    (d : Test →ₗ[𝕜] OneForm)
    (Φ : Test →ₗ[𝕜] Obs)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)) :=
  {j : CurrentDensity // Φ = (pairing j).comp d}

/-- A local current density is unique if the paired exact-differential tests separate densities. -/
theorem localCurrentDensity_unique_of_separates
    {d : Test →ₗ[𝕜] OneForm}
    {Φ : Test →ₗ[𝕜] Obs}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (hsep : Function.Injective (fun j : CurrentDensity => (pairing j).comp d))
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    R₁.val = R₂.val :=
  hsep (R₁.property.symm.trans R₂.property)

end CurrentRepresentation

end ConservationLaw
