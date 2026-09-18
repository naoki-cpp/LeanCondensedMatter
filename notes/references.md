# References

Annotated reference list. One entry per source: full citation, what it is used for in this project, and any caveats about relying on it.

## Papers and books

### Linear response and Kubo–Bastin–Středa transport

- **Ryogo Kubo.** “Statistical-Mechanical Theory of Irreversible Processes. I. General Theory and
  Simple Applications to Magnetic and Conduction Problems.” *Journal of the Physical Society of
  Japan* **12**(6), 570–586 (1957). DOI:
  [10.1143/JPSJ.12.570](https://doi.org/10.1143/JPSJ.12.570).
  - **Project use:** Foundational provenance for the bounded finite-time response-as-correlation
    principle formalized in `QuantumTheory/LinearResponse/KuboFormula.lean`.
  - **Caveat:** This paper does not supply the project's later finite-dimensional spectral,
    resolvent, contact-term, or conductivity normalizations; those identifications require their
    own hypotheses and references.

- **D. A. Greenwood.** “The Boltzmann Equation in the Theory of Electrical Conduction in Metals.”
  *Proceedings of the Physical Society* **71**(4), 585–596 (1958). DOI:
  [10.1088/0370-1328/71/4/306](https://doi.org/10.1088/0370-1328/71/4/306).
  - **Project use:** Historical source for the Kubo–Greenwood terminology used in
    `SecondQuantization/Fermionic/Transport/KuboGreenwood.lean`.
  - **Caveat:** The project's Peierls contact term and finite-rate normalization come from its
    upstream derivation. Greenwood's disordered-metal calculation is not the source of those terms,
    the general Kubo–Bastin formula, or its Středa decomposition.

- **A. Bastin, C. Lewiner, O. Betbeder-Matibet, and P. Nozières.** “Quantum Oscillations of the Hall
  Effect of a Fermion Gas with Random Impurity Scattering.” *Journal of Physics and Chemistry of
  Solids* **32**(8), 1811–1824 (1971). DOI:
  [10.1016/S0022-3697(71)80147-6](https://doi.org/10.1016/S0022-3697(71)80147-6).
  - **Project use:** Primary source for the Green-function form motivating the finite-broadening
    static operator kernel `regularizedBastinOperatorIntegrand` and its downstream trace and
    physical-normalization bridges.
  - **Caveat:** The paper treats a specific random-impurity fermion gas. The project's abstract
    finite-system normalization and general vertex data are extensions rather than a verbatim
    formalization of that model.

- **P. Středa.** “Theory of Quantised Hall Conductivity in Two Dimensions.” *Journal of Physics C:
  Solid State Physics* **15**(22), L717–L721 (1982). DOI:
  [10.1088/0022-3719/15/22/005](https://doi.org/10.1088/0022-3719/15/22/005).
  - **Project use:** Physical source for the Hall-response surface/sea terminology in
    `Transport/Streda/Integration.lean` and its downstream bridge to a physical conductivity
    tensor.
  - **Caveat:** Signs and prefactors depend on charge, orientation, volume, and unit conventions.
    The traditional terms must not be presented as individually unique physical observables
    without the Bonbien–Manchon qualification below.

- **Varga Bonbien and Aurélien Manchon.** “Symmetrized Decomposition of the Kubo-Bastin Formula.”
  *Physical Review B* **102**, 085113 (2020). DOI:
  [10.1103/PhysRevB.102.085113](https://doi.org/10.1103/PhysRevB.102.085113).
  - **Project use:** Motivates keeping the project's `residualSea` remainder distinct from the
    conventional Středa-II term, whose overlap with the conventional Středa-I term is removed by
    the paper's trace-level symmetrized decomposition.
  - **Caveat:** `regularizedStredaResidualSeaOperatorKernel` is defined as an operator-level exact
    remainder. The project has not identified it directly with the paper's trace-level sea term.

### Conserving approximations and disorder transport

- **Gordon Baym and Leo P. Kadanoff.** “Conservation Laws and Correlation Functions.” *Physical
  Review* **124**(2), 287–299 (1961). DOI:
  [10.1103/PhysRev.124.287](https://doi.org/10.1103/PhysRev.124.287).
  - **Project use:** Architectural basis for deriving compatible self-energy and response-vertex
    approximations, relevant to `Transport/Disorder/SCBA.lean`, `Transport/Disorder/Ladder.lean`,
    and the planned finite charge-vertex Ward bridge.
  - **Caveat:** Sharing a covariance or disorder moment does not by itself prove that the current
    SCBA and ladder constructions form a conserving approximation. Conservation requires an
    explicit compatibility theorem.

- **N. A. Sinitsyn, A. H. MacDonald, T. Jungwirth, V. K. Dugaev, and Jairo Sinova.** “Anomalous
  Hall Effect in a Two-Dimensional Dirac Band: The Link between the Kubo–Středa Formula and the
  Semiclassical Boltzmann Equation Approach.” *Physical Review B* **75**, 045315 (2007). DOI:
  [10.1103/PhysRevB.75.045315](https://doi.org/10.1103/PhysRevB.75.045315).
  - **Project use:** Principal benchmark for bridges between generic Kubo–Středa response, the
    Massive-Dirac model, and intrinsic, side-jump, and skew-scattering contributions.
  - **Caveat:** The equivalence is established for a particular two-dimensional Dirac model and
    perturbative disorder regime, not for arbitrary abstract Kubo and Boltzmann theories.

### Thermal Wick and linked-cluster structure

- **Michel Gaudin.** “Une démonstration simplifiée du théorème de Wick en mécanique statistique.”
  *Nuclear Physics* **15**, 89–91 (1960). DOI:
  [10.1016/0029-5582(60)90285-6](https://doi.org/10.1016/0029-5582(60)90285-6).
  - **Project use:** Primary source motivating the common bosonic/fermionic thermal Wick induction
    specialized to finite configurations by `finiteGibbsExpectation_prodComp_eq_sum_pairing`.
  - **Caveat:** The argument assumes a Gaussian noninteracting equilibrium state with the required
    mode factorization. The current theorem uses `[Fintype Config]`; a full bosonic expectation needs
    a summability-aware implementation, and this is not an interacting-state Wick theorem without
    further hypotheses.

- **Donald H. Kobe.** “Linked Cluster Theorem and the Green's Function Equations of Motion for a
  Many-Fermion System.” *Journal of Mathematical Physics* **7**(10), 1806–1820 (1966). DOI:
  [10.1063/1.1704829](https://doi.org/10.1063/1.1704829).
  - **Project use:** Reference for vacuum-component cancellation and connected Green-function
    expansions, informing the generating-functional layer and future higher-point extensions.
  - **Caveat:** This is not a direct source for the current formal-log partition-series theorem and
    does not supply the analytic convergence, trace-class, or Fredholm-determinant estimates needed
    by a fully analytic source-functional theorem.

### Current definitions and Berry geometry

- **Junren Shi, Ping Zhang, Di Xiao, and Qian Niu.** “Proper Definition of Spin Current in
  Spin-Orbit Coupled Systems.” *Physical Review Letters* **96**, 076604 (2006). DOI:
  [10.1103/PhysRevLett.96.076604](https://doi.org/10.1103/PhysRevLett.96.076604).
  - **Project use:** Semantic source for treating the proper spin current as the time derivative of
    spin displacement, equivalently a conventional current plus a torque-dipole correction. This
    motivates the corrected-current and explicit ambiguity layers.
  - **Caveat:** An arbitrary exact-differential current equivalence is not automatically the Shi
    proper current unless its model-specific torque-dipole interpretation is established.

- **Naoto Nagaosa, Jairo Sinova, Shigeki Onoda, A. H. MacDonald, and N. P. Ong.** “Anomalous Hall
  Effect.” *Reviews of Modern Physics* **82**(2), 1539–1592 (2010). DOI:
  [10.1103/RevModPhys.82.1539](https://doi.org/10.1103/RevModPhys.82.1539).
  - **Project use:** Standard vocabulary and roadmap reference for intrinsic, skew-scattering, and
    side-jump mechanisms and for relating semiclassical, Kubo, and Keldysh descriptions.
  - **Caveat:** This is a secondary review. Primary papers remain the provenance for individual
    formulas, and the mechanism split is regime- and convention-dependent.

- **Di Xiao, Ming-Che Chang, and Qian Niu.** “Berry Phase Effects on Electronic Properties.”
  *Reviews of Modern Physics* **82**(3), 1959–2007 (2010). DOI:
  [10.1103/RevModPhys.82.1959](https://doi.org/10.1103/RevModPhys.82.1959).
  - **Project use:** Standard reference for Berry connection, Berry curvature, anomalous velocity,
    and semiclassical transport. It supports a specialization bridge from the generic spectral
    Berry API to the Massive-Dirac closed form.
  - **Caveat:** Many formulas assume a smooth isolated nondegenerate band and use local gauges.
    Degeneracies, global gauge patching, and the project's totalized definitions require separate
    hypotheses.

## Lean / Mathlib resources

(To be filled)
