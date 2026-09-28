# Historical review coverage

This index records the sequential review requested for the ADR reconstruction. The initial pass read PRs #1–#16. Following the user's refinement, the continuing pass prioritizes issues in ascending number order, saving each ADR disposition before reading the next issue. PRs are consulted only when needed to verify an issue's decision or implementation. It is a coverage record, not evidence that every historical proposal remains accepted. Discussion links in individual ADRs supply the historical evidence; current Lean code remains authoritative.

| Number | Source | ADR disposition |
|---|---|---|
| 1 | [Minimal axiomatic QM foundations](https://github.com/naoki-cpp/LeanCondensedMatter/pull/1) | Extended ADR 0003: definitions versus postulates, initial finite-dimensional limitation, and rank-one embedding versus mixed-state purification. |

| 2 | [CI badge and sorry check](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2) | Extended ADR 0010: proof completeness is a CI contract; the original text search is not the current enforcement mechanism. |

| 3 | [Generated API documentation badge](https://github.com/naoki-cpp/LeanCondensedMatter/pull/3) | README navigation only; no new architectural decision. No substantive ADR change. |

| 4 | [Entropy and canonical distribution](https://github.com/naoki-cpp/LeanCondensedMatter/pull/4) | Extended ADRs 0003 and 0004: precise variational interpretation, noncommuting competitor states, and the domain obligations hidden by totalized logarithms. |

| 5 | [Partition lattice adapter](https://github.com/naoki-cpp/LeanCondensedMatter/pull/5) | Extended ADRs 0001 and 0008: recorded library comparison and separation of abstract inversion from closed-form coefficients. |

| 6 | [Gibbs bound attainment](https://github.com/naoki-cpp/LeanCondensedMatter/pull/6) | Extended ADR 0003: distinguish a bound, attainment, and uniqueness; eigenbasis ordering is not a physical constraint. |

| 7 | [Functional-calculus eigenvector bridge](https://github.com/naoki-cpp/LeanCondensedMatter/pull/7) | Added ADR 0011: define operator functions independently of finite eigenvalue enumeration; keep analytic obligations separate. |

| 8 | [Compact self-adjoint eigenvector family](https://github.com/naoki-cpp/LeanCondensedMatter/pull/8) | Extended ADR 0003: exclude the zero eigenspace from spectral trace indexing; distinguish orthonormal-family construction from countability and reconstruction. |

| 9 | [Countability of the eigenvector index](https://github.com/naoki-cpp/LeanCondensedMatter/pull/9) | Extended ADR 0003: derive countability of nonzero spectral support from compactness rather than assuming ambient separability. |

| 10 | [Supported spectral subspace](https://github.com/naoki-cpp/LeanCondensedMatter/pull/10) | Extended ADR 0003: the nonzero eigenvectors span the kernel's orthogonal complement, not necessarily the entire space. |

| 11 | [Spectral reconstruction](https://github.com/naoki-cpp/LeanCondensedMatter/pull/11) | Added ADR 0012, consolidating #8–#11: supported Hilbert basis, vectorwise reconstruction, and separate trace-class obligations. |

| 12 | [Spectral trace-class predicate](https://github.com/naoki-cpp/LeanCondensedMatter/pull/12) | Extended ADR 0012: eigenvalue multiplicities avoid basis-choice dependence; distinguish the spectral model from general Schatten theory. |

| 13 | [Spectral trace](https://github.com/naoki-cpp/LeanCondensedMatter/pull/13) | Extended ADR 0012: a spectral trace definition does not supply cross-operator linearity/cyclicity; bypassing a prerequisite is not permanently excluding it. |

| 14 | [Trace scalar-linearity performance report](https://github.com/naoki-cpp/LeanCondensedMatter/pull/14) | Closed without merging. Reported a suspected elaboration/performance problem, with no Lean change; not evidence of an accepted representation decision. No substantive ADR change. |

| 15 | [Trace scalar linearity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/15) | Extended ADR 0012: base-eigenvalue/finite-multiplicity decomposition avoids costly dependent-index transport; supported by a merged implementation. |

| 16 | [Trace additivity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/16) | Extended ADR 0012 from the already-read PR body: shared Hilbert-basis comparison and genuine convergence witnesses. |

The issue-only index starts at **#257**; lower-numbered PRs beyond #16 were not individually reviewed in the continuing pass.

| Issue | Source | ADR disposition |
|---|---|---|
| 257 | [Reuse sigma/product distribution](https://github.com/naoki-cpp/LeanCondensedMatter/issues/257) | Extended ADR 0001: reverse or compose canonical Mathlib equivalences instead of duplicating them. |

| 258 | [Canonical pair endpoints](https://github.com/naoki-cpp/LeanCondensedMatter/issues/258) | Extended ADR 0002: use equivalence injectivity and one endpoint implementation; historical compatibility allowances do not override the current policy. |

| 259 | [Normalized crossing-pair representation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/259) | Extended ADR 0008: canonical subtypes carry membership and enable structural transport instead of repeated coordinate proofs. |

| 260 | [Algebraic finite-sum parity](https://github.com/naoki-cpp/LeanCondensedMatter/issues/260) | Proof-level application of ADR 0001's Mathlib reuse rule. The issue proposes either Nat.ModEq or ZMod 2; it does not establish a permanent choice between them. No new architectural constraint. |

| 261 | [Diagonal/off-diagonal finite-sum decomposition](https://github.com/naoki-cpp/LeanCondensedMatter/issues/261) | Local proof refactor using standard Finset structure; supports ADR 0001 but does not justify freezing an induction-free proof strategy. No substantive ADR change. |

| 262 | [Product-equivalence sum reindexing](https://github.com/naoki-cpp/LeanCondensedMatter/issues/262) | Extended ADR 0002: generic helpers need upstream ownership and demonstrated reuse, even when first needed by fermionic proofs. |

| 271 | [Ordered component-leg embedding](https://github.com/naoki-cpp/LeanCondensedMatter/issues/271) | Extended ADR 0008: bundle order preservation/reflection needed for crossing transport. |

| 272 | [Subtype restriction for component pairs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/272) | Extended ADR 0008: derive pair transport by predicate-compatible restriction of ambient equivalences. |

| 273 | [Crossing transport embeddings](https://github.com/naoki-cpp/LeanCondensedMatter/issues/273) | Extended ADR 0008: embedding into internal crossings is distinct from a global crossing equivalence. |

| 274 | [Subtype product adapters](https://github.com/naoki-cpp/LeanCondensedMatter/issues/274) | Local application of ADRs 0001–0002: use generic big-operator bridges and keep any reusable helper upstream. No independent architectural decision. |

| 275 | [Global crossing sum reindexing](https://github.com/naoki-cpp/LeanCondensedMatter/issues/275) | Proof-level instance of canonical equivalence reuse and removal of unnecessary assumptions. Existing ADRs 0001, 0002, and 0008 cover the rationale; no new proof-script constraint. |

| 276 | [Diagram transport cleanup scope](https://github.com/naoki-cpp/LeanCondensedMatter/issues/276) | Extended ADR 0008: structural refactors preserve physical normalization and sign conventions; composability is the objective. |

| 281 | [Analysis and Mathlib audit](https://github.com/naoki-cpp/LeanCondensedMatter/issues/281) | Read the complete discussion. Extended ADRs 0002 and 0012: explicit switch away from compatibility layers, semantic names for spectral summability, and direct bundled hypotheses. |

| 285 | [Quartic amplitude factorization](https://github.com/naoki-cpp/LeanCondensedMatter/issues/285) | Extended ADR 0008: physical weight multiplicativity requires contraction, integration/order, and prefactor bridges. |

| 286 | [Duplicate amplitude tracker](https://github.com/naoki-cpp/LeanCondensedMatter/issues/286) | Explicit duplicate of #285; no additional decision or ADR change. |

| 290 | [Connected Dyson cumulants](https://github.com/naoki-cpp/LeanCondensedMatter/issues/290) | Extended ADR 0008: instantiate generic connected combinatorics through physical weight/moment bridges; preserve the nonempty-set scope. |

| 294 | [Formal log and finite-set cumulants](https://github.com/naoki-cpp/LeanCondensedMatter/issues/294) | Extended ADR 0008: generic ownership of factorial normalization, unit constant term, and positive-degree scope. |

| 298 | [Formal fermionic linked-cluster endpoint](https://github.com/naoki-cpp/LeanCondensedMatter/issues/298) | Extended ADR 0008: explicit separation from convergence, analytic partition functions, and thermodynamic limits. |

| 302 | [Synchronize formal linked-cluster status](https://github.com/naoki-cpp/LeanCondensedMatter/issues/302) | Documentation synchronization reiterating #298's scope. ADR 0008 already records the boundary; historical theorem names are not restored. |

| 306 | [Analytic linked-cluster connection](https://github.com/naoki-cpp/LeanCondensedMatter/issues/306) | Extended ADR 0008: ordered analytic bridge from finite formal coefficients to operator exponentials and log derivatives, gated on abstraction/library preflight. |

| 307 | [Finite analytic operator bridge](https://github.com/naoki-cpp/LeanCondensedMatter/issues/307) | Extended ADR 0005: transport algebraic maps to a normed finite realization; keep operator-integration compatibility explicit and reuse upstream Mathlib APIs. |

| 308 | [Dyson coefficient norm bounds](https://github.com/naoki-cpp/LeanCondensedMatter/issues/308) | Extended ADR 0008: use explicit sufficient factorial majorants for convergence; sharp constants are not required. |

| 309 | [Convergent analytic Dyson evolution](https://github.com/naoki-cpp/LeanCondensedMatter/issues/309) | Extended ADR 0008: require genuine operator convergence, justified integral interchange, and Volterra characterization before identifying analytic evolution. |

| 310 | [Operator exponential identity](https://github.com/naoki-cpp/LeanCondensedMatter/issues/310) | Extended ADR 0008: derive the interaction-picture identity for noncommuting interactions through uniqueness; preserve operator order. |

| 311 | [Analytic partition-function series](https://github.com/naoki-cpp/LeanCondensedMatter/issues/311) | Extended ADR 0008: justify trace/series exchange and nonvanishing before passing to analytic logarithms, preserving formal coefficients. |

| 312 | [Analytic linked-cluster log derivatives](https://github.com/naoki-cpp/LeanCondensedMatter/issues/312) | Extended ADR 0008: local analytic logarithm, Taylor-series match, and factorial-to-derivative bridge at nonzero order. |

| 315 | [Analytic-Dyson preflight](https://github.com/naoki-cpp/LeanCondensedMatter/issues/315) | Extended ADRs 0001, 0002, and 0005: reuse pinned Mathlib APIs, extract statistics-independent finite Dyson layers to Common, and prove integral compatibility before analytic transport. |

| 316 | [Canonical formal logarithm](https://github.com/naoki-cpp/LeanCondensedMatter/issues/316) | Extended ADR 0001: use `PowerSeries.logOf` as the sole formal-log construction and keep only independent normalization utilities. |

| 317 | [Common Dyson recursion](https://github.com/naoki-cpp/LeanCondensedMatter/issues/317) | Extended ADR 0002: generic finite-configuration recursion belongs in Common; fermionic corollaries stay downstream. Initial wrapper proposal was superseded by #281 policy. |

| 318 | [Common finite Dyson trace series](https://github.com/naoki-cpp/LeanCondensedMatter/issues/318) | Extended ADRs 0002 and 0007: abstract finite configuration traces while retaining a summability-aware boundary for infinite bosonic occupations. |

| 319 | [Validate the finite analytic realization](https://github.com/naoki-cpp/LeanCondensedMatter/issues/319) | Extended ADR 0005: prove coefficientwise/Bochner integral agreement before migrating consumers; preserve the established algebraic coefficient semantics. |

| 345 | [Canonical SecondQuantization architecture](https://github.com/naoki-cpp/LeanCondensedMatter/issues/345) | Extended ADRs 0002 and 0007: canonical import and namespace ownership, deletion of compatibility-only routes, invariant checks, and delaying Bosonic perturbation pending valid analytic foundations. |

| 348 | [Bosonic algebra module move](https://github.com/naoki-cpp/LeanCondensedMatter/issues/348) | Mechanical application of #345's canonical hierarchy: preserve declarations while deleting old paths without forwarding modules. No additional decision. |

| 349 | [Bosonic module migration tracker](https://github.com/naoki-cpp/LeanCondensedMatter/issues/349) | Implementation tracker for #348; no independent design decision. |

| 350 | [R4 placeholder cleanup](https://github.com/naoki-cpp/LeanCondensedMatter/issues/350) | Administrative placeholder closed immediately; no design decision. |

| 352 | [SecondQuantization architecture checks](https://github.com/naoki-cpp/LeanCondensedMatter/issues/352) | Extended ADR 0010: enforce current ownership/dependency direction as a structural contract. |

| 354 | [Remove Dyson forwarding declarations](https://github.com/naoki-cpp/LeanCondensedMatter/issues/354) | Applied #281's canonical-API rule: migrate consumers, then delete the forwarding module without replacement aliases. No new constraint. |

| 356 | [Delete discrete Dyson forwarding module](https://github.com/naoki-cpp/LeanCondensedMatter/issues/356) | Applied canonical ownership and complete migration while preserving recursion/sign/normalization conventions. ADRs 0002 and 0008 already cover these constraints. |

| 358 | [Delete continuous Dyson forwarding module](https://github.com/naoki-cpp/LeanCondensedMatter/issues/358) | Applied ADRs 0002 and 0005: use Common analytic operators directly while preserving explicit finite-dimensional/convergence assumptions. |

| 360 | [Fermionic namespace ownership](https://github.com/naoki-cpp/LeanCondensedMatter/issues/360) | Extended ADR 0002: namespace and canonical type names express API ownership; migrate callers without aliases. |

| 364 | [Finite transport and impurity roadmap](https://github.com/naoki-cpp/LeanCondensedMatter/issues/364) | Extended ADR 0009: separate physical conductivity adapters, generic supplied-Green ladder and finite SCBA bridge; record finite-scope limits. |

| 365 | [Bounded transport data and dimension](https://github.com/naoki-cpp/LeanCondensedMatter/issues/365) | Extended ADR 0009: separate Hilbert dimension, physical volume, and trace regime; current observables precede source/contact specialization. |

| 366 | [Dimension-independent resolvents](https://github.com/naoki-cpp/LeanCondensedMatter/issues/366) | Extended ADR 0009: keep bounded resolvent identities upstream of finite trace and physical-volume assumptions. |

| 367 | [Finite Kubo–Bastin derivation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/367) | Extended ADR 0009: derive from causal Kubo response, keep contact/normalization, prove the ℏη conversion, and distinguish all limits. |

| 368 | [Regularized Středa decomposition](https://github.com/naoki-cpp/LeanCondensedMatter/issues/368) | Extended ADR 0009: require convention/normalization/contact-term alignment and an explicit finite Peierls Ward identity before response decomposition. |

| 369 | [Finite transport validation models](https://github.com/naoki-cpp/LeanCondensedMatter/issues/369) | Extended ADR 0009: isolate exact finite examples that test signs/normalization from general response and limit claims. |

| 370 | [Exact finite disorder average](https://github.com/naoki-cpp/LeanCondensedMatter/issues/370) | Extended ADR 0009: normalized finite ensemble over exact configuration responses, with trace interchange proved; approximations remain separate. |

| 371 | [Weak-scattering Born self-energy](https://github.com/naoki-cpp/LeanCondensedMatter/issues/371) | Extended ADR 0009: retain the exact resolvent remainder, label Born as an approximation, and expose the closure hypothesis. |

| 372 | [Conserving vertex scope](https://github.com/naoki-cpp/LeanCondensedMatter/issues/372) | Extended ADR 0009: final scope is a finite SCBA charge-vertex consistency bridge under visible assumptions, not a complete Ward–Takahashi or conductivity theorem. Recorded refinement from initial proposal. |

| 373 | [Remove unnecessary finiteness assumptions](https://github.com/naoki-cpp/LeanCondensedMatter/issues/373) | Extended ADRs 0003 and 0005: distinguish finite outcome/support requirements from ambient dimension and configuration-type finiteness. |

| 376 | [CFC and Gibbs/entropy operators](https://github.com/naoki-cpp/LeanCondensedMatter/issues/376) | Extended ADRs 0003 and 0011: transformed spectral indices need bridges; ENNReal preserves divergent entropy; compact bounded Gibbs operators force finite dimension. |

| 384 | [Refresh analytic LCT status](https://github.com/naoki-cpp/LeanCondensedMatter/issues/384) | Documentation synchronization of #345 and #306; ADRs already record the scope. No additional decision. |

| 387 | [Fold ComponentPairs into owner](https://github.com/naoki-cpp/LeanCondensedMatter/issues/387) | Proof-internal module consolidation applying #345's semantic ownership rule. The theorem statement remains unchanged; no new decision. |

| 389 | [Fold crossing parity into owner](https://github.com/naoki-cpp/LeanCondensedMatter/issues/389) | Proof-internal consolidation under #345; declaration semantics unchanged. No new ADR. |

| 391 | [Fold leg inversion into crossing owner](https://github.com/naoki-cpp/LeanCondensedMatter/issues/391) | Proof-internal module consolidation under #345; no public statement or design change. No new ADR. |

| 393 | [Diagonal trace-class operators from summable weights](https://github.com/naoki-cpp/LeanCondensedMatter/issues/393) | Added ADR 0013: construct a discrete heat operator from an energy basis and summable Boltzmann weights rather than model an unbounded Hamiltonian as bounded. |

| 397 | [Remove component-order forwarding module](https://github.com/naoki-cpp/LeanCondensedMatter/issues/397) | Applies #345 ownership cleanup: call Common directly and remove the forwarding path. No new decision. |

| 399 | [Remove component-decomposition forwarder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/399) | Applies ADR 0002: consume Common's canonical decomposition and remove the Fermionic routing module. No new decision. |

| 401 | [Remove ordered-simplex forwarder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/401) | Applies ADR 0002: consume the canonical Common order/integration API; remove the duplicate route without changing semantics. |

| 404 | [Remove component-order forwarder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/404) | Duplicate of the canonical-owner cleanup in #345; no new design decision. |

| 406 | [Remove component-partition forwarder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/406) | Applies #345/ADR 0002: one Common owner for shared diagram decomposition. No new decision. |

| 407 | [Diagonal density-state APIs for Gibbs entropy](https://github.com/naoki-cpp/LeanCondensedMatter/issues/407) | Extended ADR 0003: factor Hilbert-basis normalization, weights, entropy, and energy as reusable state-level results. |

| 410 | [Remove component-restriction forwarder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/410) | Applies ADR 0002: canonical Common restriction API; forwarding path deleted. No new decision. |

| 412 | [Finite entropy to spectral-trace bridge](https://github.com/naoki-cpp/LeanCondensedMatter/issues/412) | Extended ADR 0003: share Hilbert-basis entropy semantics across finite and trace-class APIs; remove characteristic-polynomial eigenvalue matching. |

| 414 | [Remove reassembly forwarding cluster](https://github.com/naoki-cpp/LeanCondensedMatter/issues/414) | Applies #345/ADR 0002: diagrams use Common reassembly ownership; no compatibility modules. No new decision. |

| 416 | [Canonical ordered-diagram API](https://github.com/naoki-cpp/LeanCondensedMatter/issues/416) | Supports ADRs 0002/0008: order and diagram data are Common; Fermionic owns signs/amplitudes. Broader call-site migration got its own scope; no new decision. |

| 417 | [Remove Bosonic component forwarder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/417) | Applies ADR 0002: generic component decomposition belongs in Common while Bosonic weights remain local. No new decision. |

| 419 | [Reduce Bosonic diagram API to semantic aliases](https://github.com/naoki-cpp/LeanCondensedMatter/issues/419) | Supports ADRs 0002/0008: Common owns generic diagram structure; the statistics-specific alias survives as a distinct semantic specialization. |

| 421 | [Density-state thermal expectation architecture](https://github.com/naoki-cpp/LeanCondensedMatter/issues/421) | Extended ADRs 0006 and 0007: density expectation is canonical; coordinate sums are proof bridges; generic KMS pairing recursion has no finite-config assumption. |

| 422 | [Remove Wick diagram structural forwards](https://github.com/naoki-cpp/LeanCondensedMatter/issues/422) | Applies ADR 0002: retain the Fermionic physical alias/instances and use Common structural API directly. No new decision. |

| 427 | [Final API ownership audit](https://github.com/naoki-cpp/LeanCondensedMatter/issues/427) | Extended ADR 0002: remove confirmed forwards, but retain modules with genuine physical specialization or analytic responsibility after individual review. |

| 432 | [Post-LCT formalization program](https://github.com/naoki-cpp/LeanCondensedMatter/issues/432) | Extended ADRs 0004 and 0008: lossless-real equality-case architecture and final external-leg LCT route; independent research lines keep focused roadmaps. |

| 433 | [feat(lct): add low-order fermionic n = 1,2,3 regression corollaries](https://github.com/naoki-cpp/LeanCondensedMatter/issues/433) | Extended ADRs 0008 and 0010: low-order examples make factorial/sign conventions and formal/analytic agreement visible as regression theorems without replacing the general LCT result. |

| 434 | [research(lct): extend connected expansions to time-ordered correlations with external legs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/434) | Extended ADR 0008: the finite-mode two-point endpoint uses a.e. time covariance, one total-sum reindex and coefficientwise vacuum cancellation; exact equal-time transport and a broader source-functional API were unnecessary. |

| 435 | [research(bosonic): build a convergence-aware Gibbs, Dyson, and diagram interface](https://github.com/naoki-cpp/LeanCondensedMatter/issues/435) | Extended ADRs 0005–0007: arbitrary-configuration Dyson columns use finite reachable support; the generic KMS recursion stays representation-free; bosonic summability, domains, and analytic interchange remain explicit backend obligations. |

| 436 | [feat(combinatorics): prove the explicit partition-lattice Möbius factorial formula](https://github.com/naoki-cpp/LeanCondensedMatter/issues/436) | Extended ADR 0008: generic inversion remains independent of coefficient expansion; a dedicated partition module supplies the closed interval formula and correct empty-lattice case. |

| 437 | [feat(quantum): define and prove purity for canonical density operators](https://github.com/naoki-cpp/LeanCondensedMatter/issues/437) | Extended ADR 0003: purity is the squared-eigenvalue sum on the canonical dimension-independent density state; purity one characterizes rank one, and only the matrix-trace bridge needs finite dimension. |

| 438 | [feat(quantum): prove Gibbs-state attainment and uniqueness for Helmholtz free energy](https://github.com/naoki-cpp/LeanCondensedMatter/issues/438) | Extended ADRs 0003 and 0013: bounded Gibbs variational attainment and equality characterization need explicit hypotheses and do not prove unbounded infinite-dimensional thermal theory. |

| 439 | [research(analysis): design Hilbert–Schmidt and Fredholm operator-ideal APIs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/439) | Added ADR 0014: keep the Hilbert–Schmidt layer, general trace-class boundary, and absolutely summable diagonal Fredholm determinant within their proved domains. |

| 440 | [research(second-quantization): define the completed-space and infinite-mode extension boundary](https://github.com/naoki-cpp/LeanCondensedMatter/issues/440) | Extended ADRs 0005 and 0006: completed fermions use `ℓ²(Finset Mode)` with a dense algebraic core and explicit unbounded domains; bounded Gibbs/KMS rotation needs no generic unbounded-product API, and approximation topologies stay explicit. |

Issues #441 and #442 are pull requests, so they are skipped in this issue-focused pass.

| 443 | [feat(linear-response): derive the causal Kubo formula from time-dependent perturbations](https://github.com/naoki-cpp/LeanCondensedMatter/issues/443) | Extended ADR 0009: causal response is derived from bounded time-dependent perturbation theory, with explicit source/frequency conventions, summability, limit order, and spectral/domain scope. |

| 444 | [feat(transport): derive conductivity response from the general Kubo theorem](https://github.com/naoki-cpp/LeanCondensedMatter/issues/444) | Extended ADR 0009: conductivity consumes a continuity-linked physical current and explicit source coupling; source-dependent currents contribute contact terms, while the first theorem remains finite-volume and finite-rate. |

Issues #445–#462 are pull requests, so they are skipped in this issue-focused pass.

| 463 | [refactor(analysis): extract a dimension-independent Dyson–Volterra core](https://github.com/naoki-cpp/LeanCondensedMatter/issues/463) | Extended ADRs 0002 and 0008: Analysis owns bounded Dyson–Volterra mathematics; finite SecondQuantization keeps only its genuine representation bridge, with obsolete finite wrappers deleted after migration. |

Issues #464–#476 are pull requests, so they are skipped in this issue-focused pass.

| 477 | [feat(fermionic): derive free Gibbs entropy from the diagonal density state](https://github.com/naoki-cpp/LeanCondensedMatter/issues/477) | Extended ADR 0003: specialize entropy through the canonical Gibbs density state and generic diagonal-entropy bridges; retain the shared `0 * log 0` convention and avoid a parallel Gibbs-functional API. |

Issues #478–#480 are pull requests, so they are skipped in this issue-focused pass.

| 481 | [feat(quantum): extend trace-class POVMs to countable discrete outcomes](https://github.com/naoki-cpp/LeanCondensedMatter/issues/481) | Added ADR 0015: generalize the one POVM type to countable outcomes with pointwise-strong normalization; use the canonical density expectation and derive the finite API as a specialization. |

Issue #482 is a pull request, so it is skipped in this issue-focused pass.

| 483 | [refactor(quantum): make density theory the canonical API](https://github.com/naoki-cpp/LeanCondensedMatter/issues/483) | Extended ADRs 0002 and 0003: one responsibility-based density architecture owns expectations, countable POVMs, entropy, Gibbs results, and finite-dimensional bridges; audits reject duplicate models and legacy exports. |

Issues #484–#512 are pull requests, so they are skipped in this issue-focused pass.

| 513 | [chore: make lake lint pass repository-wide](https://github.com/naoki-cpp/LeanCondensedMatter/issues/513) | Extended ADR 0010: enable the repository-wide lint gate only after clearing the baseline; inspect simp-normal-form changes semantically and justify any narrow unused-argument suppression. |

Issues #514–#523 are pull requests, so they are skipped in this issue-focused pass.

| 524 | [feat(second-quantization): construct fermionic fields and derive conserved current](https://github.com/naoki-cpp/LeanCondensedMatter/issues/524) | Extended ADRs 0005 and 0009: build smeared fields and `dΓ` basis-independently, derive current from continuity before lattice/Peierls specialization, and use only an explicit bounded bridge into Kubo response. |

| 525 | [refactor: organize remaining targeted lint and API cleanup](https://github.com/naoki-cpp/LeanCondensedMatter/issues/525) | Extended ADR 0010: lint exceptions can encode erased domain/integrability witnesses, and simp-normal-form changes can alter proof behavior; review these API signals deliberately. |

Issues #526–#531 are pull requests, so they are skipped in this issue-focused pass.

| 532 | [refactor: centralize reusable Dyson, quartic-vertex, and AlgebraicFock APIs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/532) | Extended ADRs 0002 and 0005: share only genuinely generic Dyson, Common quartic-leg, and basis facts; retain CAR/CCR and distinct Fock representations behind their proven semantic boundaries. |

Issues #533–#534 are pull requests, so they are skipped in this issue-focused pass.

| 535 | [ci: remove unused DecidableEq parameters from two-point pairing expansion](https://github.com/naoki-cpp/LeanCondensedMatter/issues/535) | Extended ADR 0010: remove unnecessary public typeclass parameters and keep `classical` proof-local instead of globally suppressing `unusedArguments` warnings. |

Issues #536–#552 are pull requests, so they are skipped in this issue-focused pass.

| 553 | [refactor(quantum): make physical scalar types explicit and lift avoidable finite-dimensional restrictions](https://github.com/naoki-cpp/LeanCondensedMatter/issues/553) | Extended ADRs 0004 and 0010: real observable/probability types use lossless bridges, diagonal formulas generalize to countable bases, and a source audit guards public physical definitions against `.re` information loss. |

| 554 | [refactor(second-quantization): remove the unused finite-mode assumption from core mode labels](https://github.com/naoki-cpp/LeanCondensedMatter/issues/554) | Extended ADRs 0005 and 0010: foundational finite-support Fock layers accept arbitrary mode types; finite assumptions stay only where downstream proofs enumerate, and a mode-boundary audit guards the split. |

| 555 | [research(quantum): design genuine infinite-dimensional Gibbs states for unbounded Hamiltonians](https://github.com/naoki-cpp/LeanCondensedMatter/issues/555) | Added ADR 0016: normalize positive trace-class heat data through the canonical density-state API; keep unbounded Hamiltonian construction, pure-point integrability, and the noncommuting variational theorem as explicit separate boundaries. |

| 556 | [research(quantum): introduce physical PureState via rank-one density operators](https://github.com/naoki-cpp/LeanCondensedMatter/issues/556) | Extended ADR 0003: distinguish vector representatives from physical pure states, represent the latter by rank-one density operators, and avoid a redundant phase quotient. |

Issues #557–#579 are pull requests, so they are skipped in this issue-focused pass.

| 580 | [feat(quantum): complete bounded one-particle dynamics](https://github.com/naoki-cpp/LeanCondensedMatter/issues/580) | Extended ADR 0003: add bounded Schrödinger/Heisenberg and density-state evolution, equations of motion, and conservation laws on the canonical state APIs; keep unbounded dynamics and ray quotients out of scope. |

Issues #581–#634 are pull requests, so they are skipped in this issue-focused pass.

| 635 | [feat(transport): bridge finite-frequency Bastin conductivity to the static Středa integral](https://github.com/naoki-cpp/LeanCondensedMatter/issues/635) | Extended ADR 0009: exact finite-rate response identification retains the Peierls contact and volume factors and exposes the model-specific static Ward identity; no DC or thermodynamic limit follows. |

Issues #636–#658 are pull requests, so they are skipped in this issue-focused pass.

| 659 | [research(analysis): define an infinite-dimensional diagonal Fredholm determinant slice](https://github.com/naoki-cpp/LeanCondensedMatter/issues/659) | Extended ADR 0014: define the first infinite-dimensional determinant on absolutely summable diagonal data, prove reindexing/kernel results, and keep spectral trace, trace-log, and general trace-class claims separate. |

Issues #660–#676 are pull requests, so they are skipped in this issue-focused pass.

| 677 | [research(analysis): connect diagonal Fredholm determinant to finite-dimensional det](https://github.com/naoki-cpp/LeanCondensedMatter/issues/677) | Extended ADR 0014: finite-dimensional agreement is a compatibility theorem via Mathlib's matrix determinant and the diagonal specialization; it does not define the infinite product. |

Issues #678–#686 are pull requests, so they are skipped in this issue-focused pass.

| 687 | [feat(impurity): formalize the finite Born retarded–advanced ladder vertex](https://github.com/naoki-cpp/LeanCondensedMatter/issues/687) | Extended ADR 0009: the supplied-Green RA ladder uses the exact Born second-moment map and is resummed only under explicit invertibility; physical Ward/conductivity claims remain downstream. |

| 688 | [feat(impurity): prove finite SCBA charge-vertex Ward consistency](https://github.com/naoki-cpp/LeanCondensedMatter/issues/688) | Extended ADR 0009: a finite Ward-consistency bridge uses explicit charge symmetry and the generic corrected-vertex API; it does not claim nonlinear SCBA convergence or the full electromagnetic identity. |

Issues #689–#693 are pull requests, so they are skipped in this issue-focused pass.

| 694 | [research(analysis): characterize zeros of the diagonal Fredholm determinant](https://github.com/naoki-cpp/LeanCondensedMatter/issues/694) | Extended ADR 0014: the determinant-zero/kernel criterion uses explicit absolute summability and the established infinite-product APIs; it does not generalize to unconstrained totalized products. |

Issues #695–#696 are pull requests, so they are skipped in this issue-focused pass.

| 697 | [research(lct): factor two-point Wick amplitudes over external and vacuum components](https://github.com/naoki-cpp/LeanCondensedMatter/issues/697) | No new ADR decision: the issue was closed after audit because the requested fixed-time external × vacuum factorization already exists and is covered by ADR 0008/#434; reuse it rather than duplicate the layer. |

| 698 | [research(lct): prove mixed two-point contraction locality](https://github.com/naoki-cpp/LeanCondensedMatter/issues/698) | Extended ADR 0008: `ComponentTimeEq` preserves transported endpoint contractions, giving unconditional pointwise pairing/Dyson locality with crossing locality; integration still requires separate regularity. |

Issues #699–#703 are pull requests, so they are skipped in this issue-focused pass.

| 704 | [research(lct): establish analytic regularity of canonical component factors](https://github.com/naoki-cpp/LeanCondensedMatter/issues/704) | Extended ADR 0008: use chamberwise continuity, global measurability/bounds, and finite-mode simplex integrability; component shuffles need measurable locally bounded integrands, not false global continuity. |

| 705 | [Formalize the continuum Schrödinger continuity equation and probability current](https://github.com/naoki-cpp/LeanCondensedMatter/issues/705) | Extended ADR 0009: prove continuum continuity in smooth/weak/integral stages with explicit regularity, without requiring the full self-adjoint unbounded dynamics first; gauge coupling and operator-generated evolution remain separate. |

Issues #706–#709 are pull requests, so they are skipped in this issue-focused pass.

| 710 | [temp](https://github.com/naoki-cpp/LeanCondensedMatter/issues/710) | No ADR: closed as an accidental empty issue; it tracks no work or design decision. |

| 711 | [x](https://github.com/naoki-cpp/LeanCondensedMatter/issues/711) | No ADR: closed as another accidental empty issue; it tracks no work or design decision. |

Issues #712–#718 are pull requests, so they are skipped in this issue-focused pass.

| 719 | [refactor(diagrammatics): separate pairing evaluation from finite Gibbs realization](https://github.com/naoki-cpp/LeanCondensedMatter/issues/719) | Extended ADRs 0002 and 0008: share only scalar pairing evaluation; keep backend kernels and vacuum/two-point geometries separate, with no speculative universal thermal abstraction. |

| 720 | [research(lct): fix component pairing combinatorics on mixed-order chambers](https://github.com/naoki-cpp/LeanCondensedMatter/issues/720) | Extended ADR 0008: crossing and normalized endpoint transport are combinatorially stable within a mixed-order chamber; contraction continuity and integration remain separate analytic obligations. |

Issues #721–#722 are pull requests, so they are skipped in this issue-focused pass.

| 723 | [research(lct): prove continuity of standard-leg Gibbs contractions](https://github.com/naoki-cpp/LeanCondensedMatter/issues/723) | Extended ADR 0008: fixed-leg Gibbs pair contractions factor into explicit time exponentials times a bare expectation, giving global continuity before normalized-pair transport is analyzed. |

Issues #724–#731 are pull requests, so they are skipped in this issue-focused pass.

| 732 | [research(lct): build continuous representatives for component factors on order chambers](https://github.com/naoki-cpp/LeanCondensedMatter/issues/732) | Extended ADR 0008: freeze the parameter-dependent finite pairing index and crossing weight at a base point to obtain a continuous representative valid on its order chamber. |

Issues #733–#737 are pull requests, so they are skipped in this issue-focused pass.

| 738 | [research(lct): prove mixed-order walls are Lebesgue-null](https://github.com/naoki-cpp/LeanCondensedMatter/issues/738) | Extended ADR 0008: interaction/external and interaction-coincidence walls form a finite null set, allowing a.e. analysis while preserving pointwise tie conventions. |

Issues #739–#744 are pull requests, so they are skipped in this issue-focused pass.

| 745 | [research(lct): prove component factors measurable via finite order signatures](https://github.com/naoki-cpp/LeanCondensedMatter/issues/745) | Extended ADR 0008: finite Borel order-signature fibers select continuous representatives measurably and include equal-time walls, without claiming global continuity. |

Issues #746–#747 are pull requests, so they are skipped in this issue-focused pass.

| 748 | [refactor(common diagrammatics): clarify ownership and collapse duplicated infrastructure](https://github.com/naoki-cpp/LeanCondensedMatter/issues/748) | Extended ADRs 0002 and 0008: move pairing/graph math upstream, isolate quartic operator semantics, organize diagrammatics as Quartic and TwoPoint, and remove duplicate binary/staging layers. |

Issue #749 is a pull request, so it is skipped in this issue-focused pass.

| 750 | [refactor(combinatorics): own perfect-pairing scalar evaluation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/750) | Refined ADR 0002's #719 history: the pure evaluator's final canonical owner is `Combinatorics.Pairing.evaluation`; the former Common declaration was deleted without a compatibility alias. |

Issues #751–#755 are pull requests, so they are skipped in this issue-focused pass.

| 756 | [research(lct): transport component measurability to localized integrands](https://github.com/naoki-cpp/LeanCondensedMatter/issues/756) | Extended ADR 0008: compose ambient measurability with a continuous localization embedding; do not infer boundedness or interval integrability from measurability alone. |

| 757 | [refactor(common): move quartic interaction semantics out of Diagrammatics](https://github.com/naoki-cpp/LeanCondensedMatter/issues/757) | Extended ADR 0002: separate non-time quartic interaction data from its Heisenberg-evolution theorems so diagram imports stay light; delete the obsolete paths without forwarding modules. |

Issues #758–#763 are pull requests, so they are skipped in this issue-focused pass.

| 764 | [refactor(combinatorics): extract pairing-induced vertex graphs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/764) | Extended ADR 0002: place the statistics-independent pairing/vertex graph in `Combinatorics`; diagram graph APIs specialize it, while component partitions reuse Mathlib separately. |

Issues #765–#766 are pull requests, so they are skipped in this issue-focused pass.

| 767 | [research(lct): prove localized component factors integrable on ordered simplices](https://github.com/naoki-cpp/LeanCondensedMatter/issues/767) | Extended ADR 0008: finite signature representatives yield measurable local boundedness and ordered-simplex integrability without claiming raw global continuity or discarding deterministic wall values. |

Issue #768 is a pull request, so it is skipped in this issue-focused pass.

| 769 | [refactor(diagrammatics): derive component partitions from graph reachability setoids](https://github.com/naoki-cpp/LeanCondensedMatter/issues/769) | Extended ADR 0002: use Mathlib reachability setoids and `Finpartition` constructors; keep only thin domain-facing component APIs and avoid a project-local connected-component framework. |

Issues #770–#773 are pull requests, so they are skipped in this issue-focused pass.

| 774 | [research(lct): weaken ordered-simplex shuffle theorem to integrable inputs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/774) | Extended ADR 0008: generalize the shuffle theorem to recursive integrability from measurable local boundedness; chamberwise-continuous factors no longer need a false global-continuity assumption. |

Issues #775–#778 are pull requests, so they are skipped in this issue-focused pass.

| 779 | [refactor(diagrammatics): remove obsolete two-component ordered-simplex layer](https://github.com/naoki-cpp/LeanCondensedMatter/issues/779) | Extended ADR 0008: remove the unconsumed diagram-specific binary product layer but retain generic binary analysis as an internal proof tool for the finite-family shuffle API. |

Issues #780–#781 are pull requests, so they are skipped in this issue-focused pass.

| 782 | [refactor(diagrammatics): move quartic core syntax into Quartic subtree](https://github.com/naoki-cpp/LeanCondensedMatter/issues/782) | Extended ADR 0008: group quartic syntax by domain and remove an accidental two-point-to-quartic import; migrate to authoritative paths without forwarding shims. |

Issues #783–#784 are pull requests, so they are skipped in this issue-focused pass.

| 785 | [refactor(diagrammatics): remove quartic core forwarding module paths](https://github.com/naoki-cpp/LeanCondensedMatter/issues/785) | Confirms ADR 0008's module ownership: after direct consumers migrate, delete the old flat paths without forwarding modules; two-point syntax stays independent of Quartic. |

Issues #786–#788 are pull requests, so they are skipped in this issue-focused pass.

| 789 | [refactor(diagrammatics): move quartic component core into Quartic subtree](https://github.com/naoki-cpp/LeanCondensedMatter/issues/789) | Extended ADR 0002: staged breaking moves may use temporary import-only forwarders while owners change, but the follow-up must migrate consumers and delete them. |

Issue #790 is a pull request, so it is skipped in this issue-focused pass.

| 791 | [refactor(diagrammatics): remove quartic component core forwarding paths](https://github.com/naoki-cpp/LeanCondensedMatter/issues/791) | Completes the #789 migration policy: consumers use the authoritative Quartic subtree and forwarders are deleted; audit each layer's true dependencies instead of retaining accidental imports. |

Issues #792–#798 are pull requests, so they are skipped in this issue-focused pass.

| 799 | [Formalize self-adjoint continuum Schrödinger dynamics on L²](https://github.com/naoki-cpp/LeanCondensedMatter/issues/799) | Extended ADR 0009: connect the continuity API to a domain-explicit self-adjoint Schrödinger generator and Stone evolution; require a separate Schwartz representative for pointwise regularity. |

| 800 | [Formalize gauge-covariant Schrödinger continuity and electromagnetic current](https://github.com/naoki-cpp/LeanCondensedMatter/issues/800) | Extended ADR 0009: expose minimal-coupling current conventions and gauge covariance, reuse the scalar weak-continuity layer, and keep magnetic L² self-adjointness separate. |

Issue #801 is a pull request, so it is skipped in this issue-focused pass.

| 802 | [refactor(diagrammatics): move quartic component decomposition core into Quartic subtree](https://github.com/naoki-cpp/LeanCondensedMatter/issues/802) | Extended ADR 0008: group quartic component/reassembly modules under their domain subtree and keep two-point restriction dependent only on the quartic syntax it uses, not its component machinery. |

Issues #803–#805 are pull requests, so they are skipped in this issue-focused pass.

| 806 | [refactor(diagrammatics): finish quartic component modules under Quartic subtree](https://github.com/naoki-cpp/LeanCondensedMatter/issues/806) | Extended ADR 0008: move quartic ordering/pair/product/simplex specializations under Quartic while leaving reusable shuffle and partition mathematics in Analysis/Combinatorics. |

Issues #807–#808 are pull requests, so they are skipped in this issue-focused pass.

| 809 | [refactor(diagrammatics): move two-point modules under TwoPoint subtree](https://github.com/naoki-cpp/LeanCondensedMatter/issues/809) | Extended ADR 0008: complete the separate TwoPoint subtree and expose only Quartic/TwoPoint conceptual umbrellas, without merging geometries or retaining flat forwarding paths. |

Issues #810–#814 are pull requests, so they are skipped in this issue-focused pass.

| 815 | [refactor(diagrammatics): collapse quartic reassembly proof staging](https://github.com/naoki-cpp/LeanCondensedMatter/issues/815) | Extended ADR 0002: consolidate files that only stage successive proofs into one owner while preserving public theorem statements and retaining real semantic module boundaries. |

Issues #816–#818 are pull requests, so they are skipped in this issue-focused pass.

| 819 | [research(lct): connect component shuffle sum to the fixed-diagram Dyson integral](https://github.com/naoki-cpp/LeanCondensedMatter/issues/819) | Refined ADR 0008/#434: retain covariance on injective times and use a.e. equality for the integral; abandon exact pointwise transport on coincidence walls and unnecessary per-layer lemmas. |

| 820 | [refactor(proofs): replace bespoke proof plumbing with Mathlib and stronger shared abstractions](https://github.com/naoki-cpp/LeanCondensedMatter/issues/820) | Extended ADRs 0001 and 0002: reuse canonical upstream/stronger shared results, generalize finite-index APIs, and allow destructive cleanup instead of compatibility aliases. |

| 821 | [refactor(proofs): eliminate duplicated cumulant and empty-partition proofs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/821) | Extended ADR 0001: derive low-order log statements from the shared recurrence and reuse the pinned Mathlib empty-partition instance/simp API. |

| 822 | [refactor(ordered-simplex): derive continuous family shuffle from measurable theorem](https://github.com/naoki-cpp/LeanCondensedMatter/issues/822) | Extended ADR 0008: retain one measurable-locally-bounded family-shuffle proof; keep the continuous API as a thin specialization. |

| 823 | [refactor(combinatorics): rebuild family-slot decomposition from canonical equivalences](https://github.com/naoki-cpp/LeanCondensedMatter/issues/823) | Extended ADR 0001: use Mathlib complement/image equivalences to encode head/tail slot decomposition directly instead of rebuilding bijections from case analysis. |

| 824 | [refactor(ordered-simplex): generalize family shuffle API to arbitrary finite index types](https://github.com/naoki-cpp/LeanCondensedMatter/issues/824) | Extended ADRs 0002 and 0008: make the generic shuffle accept actual finite component types, removing domain-level `Fin k` presentation and transport APIs. |

| 825 | [refactor(perfect-pairing): centralize normalized-pair transport across endpoint equivalences](https://github.com/naoki-cpp/LeanCondensedMatter/issues/825) | Extended ADR 0002: place endpoint-equivalence/partner-involution transport in pure pairing combinatorics while leaving domain-specific membership and physical restrictions downstream. |

| 826 | [refactor(diagrammatics): finish TwoPoint ownership cleanup for measurable ordered simplex](https://github.com/naoki-cpp/LeanCondensedMatter/issues/826) | Completes ADR 0008's TwoPoint subtree move: place the measurable ordered-simplex theorem with its owning module and remove the last obsolete flat path. |

Issues #827–#839 are pull requests, so they are skipped in this issue-focused pass.

| 840 | [Track Stone-theorem construction for unbounded self-adjoint Hamiltonians](https://github.com/naoki-cpp/LeanCondensedMatter/issues/840) | Extended ADR 0009: use one resolvent/Yosida strong-limit evolution API with original-domain generator laws; no unbounded Borel calculus or duplicate Stone wrapper is required. |

| 841 | [Connect continuum evolution to L² Born probability conservation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/841) | Extended ADR 0009: prove integrated probability conservation from `‖ψ‖²` and unitary evolution, independently of pointwise derivative claims. |

| 842 | [Connect continuum evolution to Schwartz weak continuity](https://github.com/naoki-cpp/LeanCondensedMatter/issues/842) | Extended ADR 0009: require an explicit Schwartz representative and pointwise Schrödinger data before deriving pointwise/weak continuity; strong `L²` evolution alone is insufficient. |

| 843 | [Temporary note: #799 bridge implementation branch planned](https://github.com/naoki-cpp/LeanCondensedMatter/issues/843) | No ADR: temporary implementation-coordination note folded into #799; it records no independent design decision. |

Issues #844–#851 are pull requests, so they are skipped in this issue-focused pass.

| 852 | [refactor: reduce remaining proof plumbing and code volume](https://github.com/naoki-cpp/LeanCondensedMatter/issues/852) | Extended ADR 0001: prefer Mathlib's sorting, list-sum, finite-equivalence, and subtype-instance APIs over locally reimplementing general algorithms. |

| 853 | [refactor(mixed-time): replace bespoke insertion sort with Mathlib finite sorting](https://github.com/naoki-cpp/LeanCondensedMatter/issues/853) | Extended ADR 0008: use Mathlib's finite sorting with the proved stable event order, preserving tie conventions and public ordered-event semantics. |

| 854 | [refactor(list): centralize flatMap block-order lemmas](https://github.com/naoki-cpp/LeanCondensedMatter/issues/854) | Extended ADR 0002: move generic list-index/block-order proofs to reusable combinatorics and leave mixed-event modules focused on domain semantics. |

| 855 | [refactor(two-point): simplify mixed event and atomic-leg enumeration](https://github.com/naoki-cpp/LeanCondensedMatter/issues/855) | Extended ADR 0002: reuse the canonical mixed-event enumeration and keep only reindexing equivalences actually needed downstream. |

| 856 | [refactor(combinatorics): replace hand-built image subtype equivalences](https://github.com/naoki-cpp/LeanCondensedMatter/issues/856) | Extended ADR 0001: use Mathlib image/set equivalences instead of reconstructing bijections with `Equiv.ofBijective` and manual proofs. |

| 857 | [refactor(fintype): simplify literal subtype finite instances](https://github.com/naoki-cpp/LeanCondensedMatter/issues/857) | Extended ADR 0001: inherit `Fintype` for subtypes of finite types instead of reconstructing it from projection injectivity. |

Issues #858–#873 are pull requests, so they are skipped in this issue-focused pass.

| 874 | [refactor(two-point): replace flattening list-sum plumbing with Mathlib](https://github.com/naoki-cpp/LeanCondensedMatter/issues/874) | Extended ADR 0001: reuse Mathlib permutation/big-operator lemmas and retain the public semantic theorem while removing private list-arithmetic scaffolding. |

Issues #875–#876 are pull requests, so they are skipped in this issue-focused pass.

| 877 | [refactor(combinatorics): unify ambient family-shuffle structures](https://github.com/naoki-cpp/LeanCondensedMatter/issues/877) | Extended ADR 0008: use one ambient-cardinality shuffle structure and derive Quartic/TwoPoint variants without repeated type transport. |

Issues #878–#879 are pull requests, so they are skipped in this issue-focused pass.

| 880 | [refactor(pairing): use Mathlib Fin deletion equivalence in sum decomposition](https://github.com/naoki-cpp/LeanCondensedMatter/issues/880) | Extended ADR 0001: use Mathlib's `finSuccAboveEquiv` for finite deletion reindexing while preserving the public sum-decomposition theorem. |

| 882 | [refactor(ordered-simplex): remove custom FinCast shim](https://github.com/naoki-cpp/LeanCondensedMatter/issues/882) | Extended ADR 0001: use `Fin.castOrderIso` directly and remove a project shim/forwarder that only wrapped Mathlib functionality. |

Issues #883–#884 are pull requests, so they are skipped in this issue-focused pass.

| 885 | [refactor(pairing): standardize nonzero position hypotheses as j ≠ 0](https://github.com/naoki-cpp/LeanCondensedMatter/issues/885) | Extended ADR 0001: standardize public predicates to Mathlib's `j ≠ 0` orientation and remove adapters/compatibility wrappers. |

Issues #886–#892 are pull requests, so they are skipped in this issue-focused pass.

| 893 | [refactor(lct): collapse two-point transport and relabel proof plumbing](https://github.com/naoki-cpp/LeanCondensedMatter/issues/893) | Extended ADR 0008: retain public/reusable mathematics and compact a.e. covariance, while folding or deleting proof-only transport layers and compatibility forwarders. |

| 894 | [research(lct): finish the external-leg theorem via binary fiber factorization and vacuum cancellation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/894) | Extended ADR 0008: use external-slot binary fibers and shuffle-summed coefficient convolution; reuse formal normalization and avoid false per-diagram component products or an unnecessary `Finpartition` route. |

Issues #895–#898 are pull requests, so they are skipped in this issue-focused pass.

| 899 | [refactor(thermal): add Pfaffian/Hafnian Gaussian evaluation backend](https://github.com/naoki-cpp/LeanCondensedMatter/issues/899) | Extended ADR 0002: proposal was superseded by the existing statistics-independent first-pair recurrence; no duplicate thermal evaluation backend was required. |

Issues #900–#902 are pull requests, so they are skipped in this issue-focused pass.

| 903 | [refactor(diagrammatics): replace Pairing sign machinery with permutations and reduce code](https://github.com/naoki-cpp/LeanCondensedMatter/issues/903) | Extended ADR 0002: remove duplicate sign infrastructure by a net-deletion criterion, retaining general pairings and exposing only a small bipartite exchange-permutation bridge. |

Issues #904–#1223 are pull requests, so they are skipped in this issue-focused pass.

| 1224 | [refactor(diagrammatics): move Dyson quartic-leg coordinate structure to Common](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1224) | Extended ADR 0002: classify finite coordinate/reindexing facts in Common and operator/Gibbs/statistics content in Fermionic; remove old forwarding APIs. |

| 1225 | [discard: accidental placeholder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1225) | No ADR change: the issue says it was an accidental placeholder with no work or design decision. |

Issues #1226–#1227 are pull requests, so they are skipped in this issue-focused pass.

| 1228 | [research(crystal): derive crystallographic structure from weak atomic configurations](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1228) | Added ADR 0017 for the implemented phases: weak labeled-site primitive, derived translations/periodicity/motif, and unsplit symmetry quotient; classification work remains open. |

Issues #1229–#1250 are pull requests, so they are skipped in this issue-focused pass.

| 1251 | [feat(transport): establish finite-table Kubo evaluation and conductivity benchmarks](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1251) | Extended ADR 0009: add theorem-equivalent scalar response/conductivity tables with explicit contact/normalization data and a model-derived exact benchmark; keep numeric approximation and limits separate. |

Issues #1252–#1266 are pull requests, so they are skipped in this issue-focused pass.

| 1267 | [research(diagrammatics): generalize the two-point linked-cluster theorem to arbitrary external insertions](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1267) | Extended ADR 0008: keep generic even-insertion diagrams separate from TwoPoint and distinguish vacuum-free from fully connected correlations; theorems remain in progress. |

Issue #1268 is a pull request, so it is skipped in this issue-focused pass.

| 1269 | [research(transport): derive anomalous Hall conductivity in the 2D massive Dirac model with disorder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1269) | Extended ADR 0009: keep the model in canonical Transport ownership, distinguish clean/Born/NCA/crossed/non-Gaussian regimes, and state sequential regulator/physical limits; crossed correction remains open. |

Issues #1270–#1271 are pull requests, so they are skipped in this issue-focused pass.

| 1272 | [feat(validation): add a gapped two-site conductivity benchmark](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1272) | Extended ADR 0009: prove a second operator-derived exact benchmark through the canonical tables; no new convention or symbolic layer. |

Issue #1273 is a pull request, so it is skipped in this issue-focused pass.

| 1274 | [refactor(diagrammatics): consolidate Quartic and TwoPoint modules around semantic owners](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1274) | Extended ADR 0002: merge one-use routing files into semantic owners and privatize wrappers; 12 files and 22 public declarations removed with theorem APIs preserved. |

Issues #1275–#1285 are pull requests, so they are skipped in this issue-focused pass.

| 1286 | [refactor(current): separate generalized-current layers and simplify dependencies](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1286) | Extended ADR 0002: enforce Analysis → QuantumTheory → Fermionic/Kubo ownership while keeping intrinsic transport, current representations, and conventional-current specialization distinct. |

Issues #1287–#1293 are pull requests, so they are skipped in this issue-focused pass.

| 1294 | [feat(orbital): connect continuum-like OAM obstruction to current representation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1294) | Extended ADR 0009: retain the generic localization-correction API when OAM fails the conventional-current commutation hypothesis; the OAM-specific bridge remains open. |

Issues #1295–#1307 are pull requests, so they are skipped in this issue-focused pass.

| 1308 | [refactor(diagrammatics): organize ownership and layers across Common/Fermionic/Bosonic](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1308) | Extended ADR 0002: retain separate physical diagram families and order generic/statistics-specific, factorization, analysis, integration, and series layers without symmetry-driven abstractions. |

Issue #1309 is a pull request, so it is skipped in this issue-focused pass.

| 1310 | [feat(berry): formalize finite-dimensional Berry geometry and Hellmann–Feynman/Born–Fock identities](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1310) | Added ADR 0018: place pointwise finite-band spectral geometry upstream of AHE, with explicit derivative data and no global gauge requirement. |

Issues #1311–#1399 are pull requests, so they are skipped in this issue-focused pass.

| 1400 | [Accidental temporary issue](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1400) | No ADR change: the issue states it was created accidentally and requires no action. |

Issues #1401–#1433 are pull requests, so they are skipped in this issue-focused pass.

| 1434 | [Connect intrinsic flux/current representations to Kubo and Kubo–Středa response](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1434) | Extended ADR 0009: feed intrinsic flux to generic Kubo first, keep current-representation independence limited to exact differentials, and require explicit correction/contact/regularized Středa boundaries. |

| 1435 | [refactor(ahe): derive massive-Dirac charge current from intrinsic-flux framework](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1435) | Extended ADR 0009: prove the canonical charge-like representative equals the existing massive-Dirac vertices while keeping the pointwise model distinct from full real-space localization data. |

Issues #1436–#1456 are pull requests, so they are skipped in this issue-focused pass.

| 1457 | [[cancelled] accidental placeholder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1457) | No ADR change: the issue states it was accidental and requires no action. |

| 1458 | [[cancelled] accidental placeholder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1458) | No ADR change: the issue states it was accidental and requires no action. |

Issues #1459–#1526 are pull requests, so they are skipped in this issue-focused pass.

| 1527 | [refactor(completed-space): extract statistics-independent completed Fock infrastructure](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1527) | Extended ADR 0005: move generic completion/diagonal/finite-Hilbert theory to Common, retain physical fermionic specializations, and avoid symmetry-only abstractions. |

Issues #1528–#1530 are pull requests, so they are skipped in this issue-focused pass.

| 1531 | [refactor(transport): consolidate generic transport ownership before AHE Phase 4](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1531) | Extended ADR 0009: establish and CI-guard neutral Kubo–Bastin/Středa/disorder owners, downstream Fermionic/model specializations, and sibling exact/Born/SCBA layers. |

Issues #1532–#1554 are pull requests, so they are skipped in this issue-focused pass.

| 1555 | [refactor(thermal): clarify representation and thermal ownership](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1555) | Extended ADR 0006: separate CompletedSpace representation from Fermionic.Thermal state/KMS recursion and retain QuantumTheory.Gibbs.PurePoint as the unique generic owner. |

Issues #1556–#1578 are pull requests, so they are skipped in this issue-focused pass.

| 1579 | [refactor(transport): simplify generic transport core after ownership consolidation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1579) | Extended ADR 0009: separate the generic Transport umbrella from model consumers, centralize generic trace and resolvent spectral owners, give pre-Středa Kubo–Bastin its own names, share disorder moments, and guard the finalized dependency boundaries. |

| 1584 | [refactor(ci): move declaration-level architecture audits into Lean](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1584) | Extended ADR 0010: assign source topology to Python and elaborated declaration/namespace/type contracts to compiled Lean audits; avoid proof-body snapshots and keep declaration-specific investigations out of permanent CI unless explicitly selected. |

| 1585 | [tmp (closed: accidental creation)](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1585) | Reviewed; accidental tooling-created placeholder with no tracked work, so no ADR change. |

| 1586 | [placeholder (closed: accidental creation)](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1586) | Reviewed; accidental tooling-created placeholder with no tracked work, so no ADR change. |

| 1596 | [refactor(transport): modularize Transport/AHE and extract reusable spectral-analysis APIs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1596) | Extended ADR 0009 with the layered owners and extraction boundary; final issue comment says the post-merge Theorem Catalog/docs job was not independently observed. |

| 1608 | [refactor(ci): harden declarative source topology audits](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1608) | Extended ADR 0010: separate allowed DAG edges from fixed source contracts, require shared Python/Lean layer classification, and keep source-level policy syntax narrowly scoped. |

| 1684 | [refactor(transport): centralize exact disorder second moment and simplify Born assumptions](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1684) | Extended ADR 0009: make the exact finite `E[V X V]` ensemble-owned, require centering only for cancellation results, and keep SCBA as a distinct supplied approximation. |

| 1690 | [refactor(transport): finish side-indexed, centering, covariance, and vertex cleanup](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1690) | Extended ADR 0009: share only orientation-neutral resolvent algebra, represent centering as a property, derive SCBA covariance from the canonical exact moment, and keep the two-vertex Kubo–Bastin term distinct from observable variation and traced Středa response. |

| 1696 | [feat(ahe): specialize scalar disorder covariance for massive Dirac](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1696) | Extended ADR 0009: specialize the exact finite moment for scalar internal-space disorder while keeping continuum white-noise closure and exact averaged Green claims separate. |

| 1699 | [feat(ahe): decompose massive-Dirac retarded/advanced Green operators in the Pauli basis](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1699) | Extended ADR 0009: derive the model Pauli propagator from the existing generic resolvent, keeping the nonzero-regulator condition explicit and the pointwise identity separate from momentum averages and Born conclusions. |

| 1704 | [feat(ahe): reduce massive-Dirac Green operators by momentum inversion symmetry](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1704) | Extended ADR 0009: use exact momentum-inversion parity to remove in-plane Pauli channels before averaging, while keeping integration, continuum normalization, UV behavior, and scattering rates as separate results. |

| 1708 | [refactor(transport): introduce generic spectral occupation and band-filling layer](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1708) | Extended ADR 0009: derive occupied regions and Fermi surfaces from scalar occupation and band energies, distinguish state probabilities from spectral occupations, and keep valence/conduction names downstream of the generic theory. |

| 1709 | [feat(ahe): define finite-cutoff continuum Born self-energy for massive Dirac](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1709) | Extended ADR 0009: keep finite-ensemble scalar covariance separate from continuum Born closure, and expose the radial cutoff, `p dp` Jacobian, disorder strength, and physical momentum measure explicitly. |

| 1714 | [refactor(ahe): move massive-Dirac operator and spectral infrastructure out of Streda](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1714) | Extended ADR 0009: assign bounded operators, currents, free system, and projector/resolvent facts to the model; retain trace and integration response identities under Středa. |

| 1718 | [refactor(streda): derive canonical traced-kernel integrability](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1718) | Extended ADR 0009: derive canonical finite-trace integrability from continuity, retain derivative integrability as an explicit analytic assumption, and preserve the generic Středa data contract. |

| 1720 | [refactor(scba): make retarded/advanced data side-indexed](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1720) | Extended ADR 0009: derive SCBA advanced data from retarded input by adjoint under `SpectralSide`, while leaving orientation-sensitive exact Born/Dyson identities explicit. |

| 1724 | [feat(ahe): factor continuum Born channels through a common denominator integral](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1724) | Extended ADR 0009: derive scalar and mass-channel integrals from one finite-cutoff radial denominator without duplicating propagator notation or claiming its later limits. |

| 1726 | [feat(transport): add longitudinal conductivity](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1726) | Extended ADR 0009: record the `σxx ∼ 1/W` Drude scaling, compare the finite `W σxx` coefficient to Born-RTA, and keep the fixed-cutoff `η → 0⁺` then `W → 0⁺` limits separate from UV and thermodynamic claims. |
| 1729 | [feat(ahe): evaluate finite-cutoff continuum Born denominator integral](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1729) | Extended ADR 0009: evaluate the shared Born denominator with a principal-log endpoint identity at finite cutoff, keeping nonzero-regulator conditions explicit and its limits separate. |
| 1734 | [feat(ahe): split finite-cutoff Born denominator integral into real and imaginary parts](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1734) | Extended ADR 0009: record exact finite-cutoff real and imaginary endpoint formulas while preserving inherited regulator assumptions and excluding large-cutoff, zero-broadening, scattering-rate, and approximation claims. |
| 1738 | [feat(ahe): expose polynomial cutoff dependence of Born denominator real part](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1738) | Extended ADR 0009: express the finite-cutoff real endpoint through the real denominator polynomial and its norm square root, without claiming an asymptotic or UV prescription. |
| 1743 | [feat(ahe): prove logarithmic UV divergence of continuum Born real part](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1743) | Extended ADR 0009: record `Re J_s → −∞` at fixed nonzero broadening and its logarithmic cutoff behavior, separate from zero-broadening and renormalization claims. |
| 1746 | [feat(ahe): take metallic zero-broadening limit of continuum Born imaginary part](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1746) | Extended ADR 0009: record the fixed-finite-cutoff metallic limit `Im J_s → −sπ/(2v²)` and preserve retarded/advanced signs without a simultaneous UV limit or scattering-rate identification. |
| 1748 | [feat(ahe): derive metallic zero-broadening limits of Born Pauli channels](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1748) | Extended ADR 0009: propagate the denominator boundary through scalar and `σ_z` Born channels, explicitly controlling the vanishing `η Re J_s` term and deferring lifetime interpretation. |
| 1751 | [feat(ahe): derive metallic Born self-energy damping coefficients](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1751) | Extended ADR 0009: propagate the channel limits through the canonical continuum measure into self-energy damping and simplify its physical-momentum prefactor, while deferring transport-lifetime and NCA claims. |
| 1753 | [feat(ahe): project Born damping onto the metallic upper band](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1753) | Extended ADR 0009: project the actual self-energy onto the gauge-independent upper-band Fermi-surface state and name its positive single-particle damping energy, distinct from transport lifetime. |
| 1757 | [feat(ahe): derive Born single-particle scattering rate](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1757) | Extended ADR 0009: derive `1/τ_sp = 2Γ_Born/ℏ` and its reciprocal lifetime from the model's damping energy, explicitly keeping it distinct from `τ_tr`. |
| 1761 | [feat(impurity): add exact finite Born RA ladder algebra](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1761) | Extended ADR 0009: put the bounded-complex-linear RA Born action in generic Transport over the canonical exact second-moment map; separate finite iterates from conditional resummation and exact-average/SCBA claims. |
| 1766 | [feat(ahe): reduce the massive-Dirac RA current rung to the in-plane Pauli basis](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1766) | Extended ADR 0009: record exact finite-broadening angular closure on `σₓ, σᵧ`, preserving `Gᴿ Γ Gᴬ` orientation and the seam between generic ladder algebra and model-specific Pauli reduction. |
| 1776 | [feat(impurity): add conditional finite ladder resummation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1776) | Extended ADR 0009: solve the generic ladder fixed-point equation and prove uniqueness only under invertibility of `I − L`, with no convergence or geometric-series claim. |
| 1778 | [feat(ahe): feed Born scalar and mass damping into the massive-Dirac propagator](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1778) | Extended ADR 0009: retain scalar energy and `σ_z` mass damping in the side-indexed Born propagator instead of collapsing it to one phenomenological broadening; keep the clean propagator and exact-disorder APIs separate. |
| 1783 | [feat(impurity): instantiate SCBA retarded-advanced ladder vertex](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1783) | ADR 0009 records the superseding design: instantiate the generic supplied-Green ladder API directly for SCBA, avoiding dedicated one-use routing/resummation wrappers. |
| 1784 | [feat(transport): add Born-dressed radial RA current rung](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1784) | Extended ADR 0009: carry both Born damping channels through the finite-cutoff, in-plane radial RA current rung, preserving the polar measure and orientation while keeping it distinct from exact averaging and conductivity. |
| 1787 | [feat(ahe): reduce the Born-dressed RA current rung to radial kernels](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1787) | Extended ADR 0009: expose explicit one-dimensional `σₓ/σᵧ` kernels with a real sum-of-squares RA denominator and orientation-sensitive transverse sign, before radial evaluation or ladder solving. |
| 1789 | [feat(ahe): evaluate the Born RA radial rung and weak-disorder limit](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1789) | Extended ADR 0009: evaluate finite-cutoff radial kernels, prove cutoff removal separately, and retain the longitudinal and scaled-transverse weak-disorder one-rung limits without asserting a joint limit or conductivity. |
| 1792 | [feat(transport): evaluate weak-disorder Born RA current rung](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1792) | Extended ADR 0009: include physical normalization in the longitudinal rung, prove its finite weak-disorder limit, and relate its inverse ladder factor to `τ_tr/τ_sp` without asserting full Kubo/RTA equivalence. |
| 1797 | [feat(transport): bridge dressed longitudinal vertex into finite-broadening Streda](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1797) | Extended ADR 0009: preserve distinct measured-bare and source-dressed current roles, establish the operator bridge before scalar ladder substitution, and keep finite-broadening traced Fermi-surface/sea data separate from later limits and RTA recovery. |
| 1799 | [feat(transport): insert Born-dressed longitudinal vertex into RA Kubo channel](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1799) | Extended ADR 0009: expose the generic RA trace and explicit RR/AA remainder; distinguish the clean finite-external-broadening identity from the then-zero-external-broadening Born propagator insertion. |
| 1802 | [feat(transport): retain external broadening in Born-dressed Green function](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1802) | Extended ADR 0009: construct a finite-external-`η` Born-Dyson candidate from the canonical scalar/`σ_z` self-energy, prove its Dyson and adjoint properties, and keep it distinct from an exact averaged Green function. |
| 1808 | [feat(ahe): solve finite-broadening in-plane Born current ladder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1808) | Extended ADR 0009: solve the finite-`η` normalized two-component ladder under an explicit determinant condition, reuse the shared in-plane algebra, and defer weak-disorder substitution and conductivity insertion. |
| 1809 | [feat(ahe): solve the in-plane ladder coefficient fixed point](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1809) | Extended ADR 0009: isolate arbitrary-coefficient two-component Pauli ladder algebra, its orientation, determinant condition, fixed-point solution, and uniqueness from continuum integral evaluation. |
| 1811 | [feat(ahe): reduce finite-eta Born-Dyson current rung to in-plane basis](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1811) | Extended ADR 0009: derive both in-plane angular actions from the finite-`η` Born-Dyson propagator and share only the reusable Pauli rung algebra between clean and Born consumers. |
| 1817 | [feat(ahe): integrate and normalize finite-eta Born-Dyson in-plane rung](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1817) | Extended ADR 0009: integrate the full-angle coefficients with `p dp`, attach disorder and physical momentum normalization once, and feed the resulting pair directly to the shared in-plane ladder. |
| 1821 | [feat(ahe): instantiate finite-eta Born-Dyson dressed current vertex](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1821) | Extended ADR 0009: instantiate the shared in-plane fixed point with normalized model coefficients, convert it to physical current through the existing operator boundary, and retain the bare zero-disorder regression without adding another authority. |
| 1827 | [feat(ahe): insert finite-eta dressed vertex into Hall Streda surface](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1827) | Extended ADR 0009: pair bare measured `jₓ` with the rotated bare-`σᵧ` dressed source, retain the RR/AA remainder, and keep the result finite-cutoff/finite-`η` before radial integration and conductivity. |
| 1840 | [refactor(transport): move massive-Dirac benchmark under Models](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1840) | Extended ADR 0009: assign ownership by model, formalism, and observable; keep generic Transport model-independent, Středa response-level, and `ConductivityTensor` generic and downstream of physical normalization. |
| 2010 | [feat(ahe): integrate finite-eta dressed Hall surface over momentum](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2010) | Extended ADR 0009: integrate and physically normalize the finite-cutoff finite-`η` ordered `xy` response, while reserving Hall terminology for the antisymmetric tensor projection. |
| 2015 | [feat(ahe): reduce finite-eta dressed Hall surface to radial form](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2015) | Extended ADR 0009: derive the complex radial coefficient with shared Pauli algebra and prove the selected isotropic off-diagonal RR/AA remainder vanishes, while keeping the result ordered and finite-`η`. |
| 2018 | [feat(transport): integrate finite-eta dressed longitudinal Streda surface](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2018) | Extended ADR 0009: add a real conductivity-level owner consuming canonical vertex and Středa trace APIs, retain bare RR/AA, normalize the physical momentum integral once, and avoid response-only forwarding shims. |

Next issue: **2021**.
