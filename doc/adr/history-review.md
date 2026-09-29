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

| 513 | [chore: make lake lint pass repository-wide](https://github.com/naoki-cpp/LeanCondensedMatter/issues/513) | Extended ADRs 0010 and 0019: enable the repository-wide lint gate only after clearing the baseline; inspect simp-normal-form changes semantically and justify any narrow unused-argument suppression. |

Issues #514–#523 are pull requests, so they are skipped in this issue-focused pass.

| 524 | [feat(second-quantization): construct fermionic fields and derive conserved current](https://github.com/naoki-cpp/LeanCondensedMatter/issues/524) | Extended ADRs 0005 and 0009: build smeared fields and `dΓ` basis-independently, derive current from continuity before lattice/Peierls specialization, and use only an explicit bounded bridge into Kubo response. |

| 525 | [refactor: organize remaining targeted lint and API cleanup](https://github.com/naoki-cpp/LeanCondensedMatter/issues/525) | Extended ADRs 0010 and 0019: lint exceptions can encode erased domain/integrability witnesses, and simp-normal-form changes can alter proof behavior; review these API signals deliberately. |

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

| 1267 | [research(diagrammatics): generalize the two-point linked-cluster theorem to arbitrary external insertions](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1267) | Extended ADR 0008: keep generic even-insertion diagrams separate from TwoPoint and distinguish vacuum-free from fully connected correlations. [PR #2715](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2715) adds higher-point mixed-time ordering, [PR #2718](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2718) adds its fermionic `TimedField` pairing consumer, [PR #2728](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2728) builds the fixed-time amplitude, [PR #2729](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2729) provides minimal component-local data, and [PR #2732](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2732) proves timed-field locality under the local-to-ambient leg embedding. Pair-contraction locality, component-product factorization, and the linked-cluster theorem remain in progress. |

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

| 1555 | [refactor(thermal): clarify representation and thermal ownership](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1555) | Extended ADRs 0005, 0006, and 0016: separate CompletedSpace representation from Fermionic.Thermal state/KMS recursion and retain QuantumTheory.Gibbs.PurePoint as the unique generic owner. |

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
| 2021 | [feat(ahe): expose finite-eta Hall radial denominator form](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2021) | Extended ADR 0009: factor the ordered complex Hall radial coefficient over a shared retarded–advanced denominator, reusing established invertibility without introducing local limits or real-part coercions. |
| 2023 | [feat(transport): derive microscopic Born-RTA longitudinal scaling](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2023) | Extended ADR 0009: instantiate the existing RTA benchmark with the microscopic Born transport lifetime and use finite `W σxx` as the weak-disorder target instead of a nonexistent finite raw limit. |
| 2027 | [feat(ahe): expose finite-cutoff Born-Dyson zero-broadening boundary](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2027) | Extended ADR 0009: combine the side-indexed complex denominator limit and propagate the fixed-disorder finite-cutoff `η → 0⁺` boundary through Born channels and Dyson denominators, preserving finite real renormalization. |
| 2028 | [temp](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2028) | No ADR change: placeholder body contains only `temp` and no comments or architectural content. |
| 2029 | [temp2](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2029) | No ADR change: placeholder body contains only `temp2` and no comments or architectural content. |
| 2030 | [noop](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2030) | No ADR change: placeholder body contains only `noop` and no comments or architectural content. |
| 2032 | [feat(transport): expose zero-broadening Born current-rung boundary](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2032) | Extended ADR 0009: carry fixed-disorder finite-cutoff broadening convergence to pointwise angular coefficients and the normalized radial integrand, without claiming convergence of the radial integral or interchanging limits. |
| 2039 | [feat(ahe): expose zero-broadening Born current-rung kernel](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2039) | Extended ADR 0009: retain the fixed-momentum complex transverse numerator `i(E_A M_R − E_R M_A)` in repository orientation and keep its radial-integrand limit separate from radial integration and ladder limits. |
| 2042 | [feat(transport): pass zero-broadening limit through Born current-rung radial integrals](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2042) | Extended ADR 0009: use compact denominator nonvanishing and dominated convergence to pass fixed-disorder finite-cutoff `η → 0⁺` through the normalized radial rung, without a weak-disorder or conductivity limit. |
| 2043 | [feat(ahe): justify zero-broadening limit through current-rung radial integrals](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2043) | ADR 0009 records the superseding shared direction-indexed convergence API; no separate X-only/Y-only wrappers are added. |
| 2057 | [feat(transport): pass zero-broadening limit through solved Born ladder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2057) | Extended ADR 0009: propagate the integrated rung boundary to the solved coefficient vector only under explicit nonzero boundary determinant regularity, still at fixed disorder/cutoff and before response insertion. |
| 2067 | [feat(transport): expose zero-broadening dressed source-current boundary](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2067) | Extended ADR 0009: propagate the indexed ladder limit through the source-indexed current operator for all in-plane directions, without restoring direction-specific wrappers or yet passing through Středa integration. |
| 2091 | [feat(transport): expose longitudinal Streda denominator form](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2091) | Extended ADR 0009: retain the full longitudinal RA/RR/AA denominator expression and prefer this multi-consumer form over a one-consumer public pointwise-limit wrapper. |
| 2096 | [feat(transport): take longitudinal Streda radial integral zero-broadening limit](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2096) | Extended ADR 0009: pass fixed-disorder `η → 0⁺` through longitudinal Středa momentum response using integrated RA rung limits and exact RR/AA endpoint primitives, without adding a second DCT layer or conductivity normalization. |
| 2099 | [refactor(transport): review MassiveDirac terminal leaf wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2099) | Extended ADRs 0002 and 0020: treat theorem-proof terminality as a candidate signal only; inspect source consumers and semantic value before cleanup, preserve independent mathematical endpoints, and retain the canonical vector-first specialization without compatibility wrappers. |
| 2102 | [refactor(streda): remove proof-only ladder regularity from values](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2102) | Extended ADR 0009: keep Středa/response values algebraic and proof-independent; require ladder regularity only where the theorem interprets solved coefficients as the physical fixed-point solution, allowing limits to target the canonical value API. |
| 2108 | [Refactor MassiveDirac transport around direction-indexed vector algebra](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2108) | Extended ADRs 0002 and 0009: reuse generic Pauli algebra from `Analysis/InternalSpace` and keep MassiveDirac ladder/current/Středa APIs on one complete indexed in-plane vector, with scalar coordinates only as projections and no type-level wrappers without a concrete consumer. |
| 2110 | [feat(transport): attach longitudinal Streda conductivity zero-broadening boundary](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2110) | Extended ADR 0009: compose the established fixed-disorder Středa momentum-integral boundary with the existing physical normalization downstream, reusing upstream convergence and adding no parallel normalization or extra limit. |
| 2126 | [feat(transport): take weak-disorder limit of zero-broadening Born-Dyson ladder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2126) | Extended ADR 0009: after forming the fixed-cutoff zero-broadening boundary at each positive disorder strength, take a separate `W → 0⁺` limit of the canonical rung vector and solved ladder/action; do not infer a conductivity limit or simultaneous `η/W` limit. |
| 2157 | [feat(transport): take weak-disorder limit of scaled longitudinal conductivity](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2157) | Extended ADR 0009: prove the sequential finite-cutoff limit of `W σxx`, combining the Středa RA ladder-action limit with vanishing `W`-weighted RR/AA endpoints, then compare through the existing normalization with the Born-RTA target. |

| 2188 | [refactor(operator): centralize ζ-commutator algebra in Analysis](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2188) | Extended ADRs 0001, 0002, and 0008 from current source: `Analysis/ScalarExchange/Basic.lean` owns the shared bracket, Common selects statistics and owns quartic local-leg exchange. The issue body names an `Analysis/Operator/ZetaCommutator` destination that is absent from current `main`, so that proposed path is not recorded as implemented. |

| 2217 | [research(topology): derive the TKNN Hall conductivity for 2D periodic crystals](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2217) | Updated ADR 0018's boundary: a global topological-transport consumer is now proposed and should reuse the crystal reciprocal/Brillouin substrate and pointwise Berry geometry. No ADR for a completed TKNN result: the issue remains open, and BZ integration/Chern integrality are still unimplemented. |

| 2232 | [research(crystal): formalize Bravais and reciprocal lattices](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2232) | Extended ADR 0017: use Mathlib's full `Submodule ℤ V` lattice substrate, encode the `2π` convention once in the physical reciprocal pairing, and keep `BrillouinTorus` a thin quotient alias owned by Crystal. The issue remains open for downstream integration. |

| 2235 | [Extend Lean metaprogramming audits beyond structural theorem cataloging](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2235) | Extended ADR 0020: keep theorem replacement, proof-region, unused-hypothesis, and retained re-audit findings advisory; retain hard CI for unambiguous correctness checks and require semantic review before changing APIs. The broader catalog/provenance issue remains open. |

| 2237 | [Replace doc-gen4 site with an interactive declaration graph explorer](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2237) | Extended ADRs 0010 and 0020: make the explorer a static view over Lean-generated catalog JSON, keep dependency extraction and semantic review data canonical in Lean, and leave audit findings advisory. Current frontend consumes the published catalog rather than reimplementing its relations. |

| 2245 | [Improve declaration graph navigation and readability](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2245) | No ADR change: this is a UX refinement of the static catalog frontend established by #2237; it preserves the catalog-as-source-of-truth boundary and adds no Lean/API architecture decision. |

| 2252 | [Render declaration neighborhoods as radial trees](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2252) | No ADR change: radial tree layout is a frontend presentation choice; the issue explicitly leaves theorem-catalog semantics and data ownership unchanged. |

| 2257 | [feat(crystal): derive a finite translation motif](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2257) | Extended ADR 0017: derive a finite motif and unique translation-motif normal form under free translation action, while keeping motif/transversal choices outside primitive `AtomicConfiguration` data. |

| 2261 | [feat(crystal): prove finite translation normal form](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2261) | Refined ADR 0017 with the generic theorem boundary `FiniteModuloTranslations + IsCancelVAdd`; periodic torsors consume the unique derived normal form directly without a specialized wrapper. |

| 2266 | [feat(crystal): derive point group from symmetry linear part](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2266) | Extended ADR 0017: derive pure translations as the kernel and the point group as the range of the symmetry linear-part homomorphism, using Mathlib's quotient-by-kernel equivalence without a split extension or duplicate group wrapper. |

| 2274 | [feat(crystal): represent point group on translation lattice](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2274) | Extended ADR 0017: use the existing translation `ℤ`-lattice for a faithful point-group representation only under full periodicity, leaving basis matrices and `GL(n, ℤ)` coordinates downstream. |

| 2377 | [refactor(thermal): own finite Gibbs partition normalization](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2377) | Extended ADRs 0003 and 0006: centralize finite-Gibbs partition nonvanishing and derive it inside normalized expectation/peeling APIs; keep exchange-denominator hypotheses explicit and retain the Statistics-facing adapter. |

| 2378 | [refactor(second-quantization): use finite operator equivalences directly](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2378) | Extended ADR 0005: consume the canonical analytic/Fock and Hilbert/Fock equivalences directly, removing only semantically empty forwarders while preserving representation-specific norm, adjoint, basis, and integral bridges. |

| 2379 | [refactor(bosonic): separate quartic occupation bounds from thermal summability](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2379) | Extended ADR 0007: keep finite occupation and particle-number facts in the algebra layer, the operator-specific `(N + 2)^2` estimate free of thermal imports, and Boltzmann summability in the Gibbs adapter; no infinite-mode claim is added. |

| 2381 | [refactor(analysis): own bounded Dyson hypotheses](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2381) | Extended ADR 0008: centralize the weak identity bound, nonnegative majorant, interval-local interaction bound, and continuity contract in `Analysis.Dyson`; retain `[0, β]` scope and construct adapters in physical consumers. |

| 2382 | [refactor(analysis): make intrinsic balance laws own semantic theorems](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2382) | Extended ADR 0002: generic transport identities belong to `IntrinsicBalanceLaw`, while `BalanceLaw` retains a chosen current extension and its shift operations; conversions stay in a dedicated adapter, with extension ambiguity explicit. |

| 2383 | [refactor(analysis): establish one normalized power-series package boundary](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2383) | Extended ADR 0008: expose the formal normalization/log/cumulant workflow through `Analysis.PowerSeries`, retain explicit coefficient hypotheses and lower Combinatorics dependencies, and keep convergence/evaluation outside this package. |

| 2384 | [refactor(analysis): unify pointwise Berry eigenbasis data](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2384) | Extended ADR 0018: use one direction-indexed pointwise eigenbasis owner for Berry connection and curvature; derive one-direction results by specialization without expanding the API to global gauge or topology. |

| 2387 | [refactor(transport): own the MassiveDirac same-side longitudinal remainder](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2387) | Extended ADR 0009: centralize the finite-broadening `RR/AA` radial remainder and its sequential endpoints in the model-local Středa layer; keep it separate from the singular `RA` ladder and conductivity normalization. |

| 2388 | [refactor(transport): move zero-broadening propagator regularity upstream](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2388) | Extended ADR 0009: make the Born-Dyson propagator boundary own the real-renormalization condition and denominator nonvanishing results, with downstream rung and Středa integrations consuming that shared guarantee under unchanged assumptions. |

| 2389 | [refactor(transport): define a coherent generic Analysis package seam](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2389) | Extended ADR 0009: document `Transport.Analysis` as the opt-in public umbrella for generic transport analysis utilities, separate from the broad Transport and model imports; narrow leaves remain available to focused consumers. |

| 2391 | [research(transport): formalize parameterized AHE universal scaling](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2391) | Extended ADR 0009: keep anomalous-Hall scaling parameterized and MassiveDirac-local, reuse normalized transport results, and distinguish implemented RTA/pair boundaries from the still-open clean-skew and intrinsic-window theorems. |

| 2393 | [research(impurity): formalize the MassiveDirac scalar-impurity T-matrix boundary](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2393) | Extended ADR 0009: keep impurity parameters, supplied loop, Born convention, and exact disorder semantics distinct; the fixed-loop remainder is not a self-consistent closure, and the physical mean-term treatment remains open. |

| 2394 | [research(transport): formalize the MassiveDirac Keldysh surface/sea response bridge](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2394) | Extended ADR 0009: make the Keldysh API a model-local adapter into the existing generic surface/sea theorem, retaining the observable-variation term and explicit regulator/normalization; the paper-faithful route remains blocked by #2393. |

| 2395 | [research(transport): define an explicit hopping-conduction AHE scaling model](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2395) | Extended ADR 0009: keep hopping conduction as a separate model gate from MassiveDirac, quantify rather than hard-code the exponent, and defer a generic scaling interface until independent consumers exist. |

| 2396 | [research(transport): align MassiveDirac with the paper's fixed-pz quadratic Hamiltonian](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2396) | Extended ADR 0009: preserve the pure-cone MassiveDirac benchmark and place the scalar-dispersive fixed-`p_z` slice in a separate model boundary with explicit parameter conventions; no 3D integration follows. |

| 2406 | [refactor(second-quantization): deepen the Common energy-shift interface](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2406) | Extended ADR 0002: keep generic energy-shift phase/composition laws in Common and the `CarriesShift` proofs in their statistics-specific owners, without crossing into completed Hilbert-space operators. |

| 2407 | [refactor(second-quantization): deepen the Bosonic Gibbs-domain adapter](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2407) | Extended ADR 0007: centralize summability-to-domain conversion and finite-sum expectation evaluation in the analytic Gibbs adapter, while keeping caller witnesses and product/integral convergence explicit. |

| 2408 | [refactor(second-quantization): separate the Bosonic KMS reindexing seam](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2408) | Extended ADR 0007: place occupation-coordinate ladder trace cyclicity in Bosonic Algebra without thermal hypotheses, then compose it with the positive-energy Gibbs/KMS adapter while retaining infinite-sum requirements. |

| 2409 | [refactor(second-quantization): centralize Bosonic polynomial occupation summability](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2409) | Extended ADR 0007: derive quadratic and total-particle-number Gibbs majorants from the general finite-mode occupation-monomial summability owner, while preserving the exact-sum API and infinite occupation-space scope. |

| 2413 | [refactor(transport): make continuum measure provenance explicit](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2413) | Extended ADR 0009: keep the generic 2D momentum measure upstream and MassiveDirac disorder, angular, and conductivity prefactors model-local; record the `2π` bridge equations and apply the measure exactly once, with trace-only normalization after crossed real-space Fourier blocks. |

| 2414 | [refactor(transport): share angular harmonic coefficient adapter](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2414) | Extended ADR 0009: use one generic constant/first/second harmonic representation for ordinary angular integration and phase-weighted polar Fourier reduction; keep explicit finite-cutoff kernels and model-specific Pauli/radial data at their respective owners. |

| 2415 | [refactor(transport): centralize MassiveDirac Born radial kernel ownership](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2415) | Extended ADR 0009: keep common Born radial denominator and RA-pair algebra in the MassiveDirac Born owner, the external measure/disorder factor in its narrow prefactor owner, and physical integrands and conclusions in their existing layers. |

| 2416 | [refactor(streda): separate shared traced-kernel facts from response proofs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2416) | Extended ADR 0009: keep abstract Streda integration data, derive shared traced-kernel regularity once, and restrict response-matrix entries to pair-specific boundary and response-equality obligations. |

| 2420 | [refactor(quantum-theory): centralize pure-point Lehmann transition data](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2420) | Extended ADR 0009: make one ordered transition record own the energy gap and physical weight across time, frequency, finite-table, and limit paths; keep scalar tables as explicit adapters and countable summability/resonance hypotheses visible. |

| 2431 | [refactor(second-quantization): centralize source-vacuum formal-series cancellation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2431) | Extended ADR 0008: put coefficientwise source/vacuum inverse cancellation in the statistics-independent formal power-series owner, while keeping the physical two-point factorization and external connectedness semantics in the Fermionic diagram layer. |

| 2435 | [refactor(combinatorics): route normalized connected expansions through NormalizedSetFunction](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2435) | Extended ADR 0008: bundle empty-set normalization for connected-decomposition object moments and route the Bosonic cumulant through `NormalizedSetFunction`, without strengthening the raw semiring-generic combinatorics layer. |

| 2436 | [refactor(transport): split band occupation from Lorentzian edge analysis](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2436) | Extended ADR 0009: separate arbitrary band-state composition, the strict zero-temperature step and band-filling predicates, and heavier Lorentzian edge integrals/limits so consumers import the narrowest needed owner. |

| 2438 | [refactor(transport): lift scalar disorder charge equivariance into generic finite Ward interface](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2438) | Extended ADR 0009: state finite SCBA/RA Ward consistency through generic `ChargeSymmetry`, with identity charge valid for any finite disorder ensemble and scalar impurity commutation only a sufficient adapter. The generic identity case was implemented by [PR #2735](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2735). |

| 2442 | [refactor(lct): canonicalize linked-cluster ownership and public API before higher-point work](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2442) | Extended ADR 0008: consolidate generic formal algebra, Fermionic perturbation/bridge, concrete quartic endpoints, and two-point physical factorization under canonical owners; keep low-order checks opt-in and higher-point work separate. |

| PR 2443 | [refactor(lct): canonicalize analytic linked-cluster ownership](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2443) | Implementation slice of #2442: moves analytic linked-cluster theorem ownership and removes proof-stage routing; its design is covered by the #2442 ADR entry, so no separate ADR was added. |

| PR 2444 | [refactor(lct): centralize source-vacuum series cancellation](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2444) | Implements #2431 and feeds the #2442 ownership gate; its generic formal-series cancellation and two-point physical factorization are already recorded in ADR 0008, so no separate ADR was added. |

| PR 2445 | [refactor(cumulant): route connected expansions through normalized set functions](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2445) | Implements #2435 under the existing `NormalizedSetFunction` boundary already captured in ADR 0008; no separate ADR was added. |

| PR 2446 | [refactor(lct): narrow formal linked-cluster public surface](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2446) | Completes another #2442 implementation slice: canonicalizes formal coefficient and quartic endpoint ownership and removes one-consumer public routes; ADR 0008 already records the ownership gate. |

| PR 2447 | [refactor(lct): localize analytic proof machinery](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2447) | Continues #2442 by hiding proof witnesses behind the semantic analytic/formal bridge; this is implementation detail under the already-recorded ownership decision. |

| PR 2448 | [refactor(lct): extract statistics-independent connected bridge](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2448) | Extended ADR 0008: use the generic formal replica bridge for the Fermionic linked-cluster endpoint while leaving the Bosonic theorem on direct normalized finite-set cumulants; avoid a redundant source-functional layer for symmetry. |

| 2449 | [research(bosonic): connect Dyson coefficients to a quartic linked-cluster theorem](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2449) | Extended ADR 0008: the physical Bosonic LCT must start from convergence-aware Dyson/Gibbs coefficients and reindex to time-integrated diagrams, preserving explicit domain obligations, global-order-sum normalization, and separation from the static averaged theorem. #2866 and #2869 implement the first bridges; component factorization remains open. |

| PR 2450 | [refactor(lct): extract generic formal connected core](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2450) | Extended ADR 0008: make `NormalizedSetFunction` the generic coefficient boundary for formal power-series LCT and keep the formal-log/connected theorem separate from genuine source-functional semantics; this becomes the intended formal endpoint for #2449. |

| PR 2451 | [refactor(lct): drop unused log constant wrapper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2451) | Removes an unused Fermionic specialization in favor of the generic `PowerSeries.constantCoeff_logOf`; this follows the generic ownership decision already captured in ADR 0008 and adds no separate architecture decision. |

| PR 2452 | [refactor(lct): trim low-order wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2452) | Implements the #2442 rule that low-order identities are opt-in examples rather than redundant connected-diagram or analytic umbrella wrappers; ADR 0008 already records this, so no separate decision was added. |

| PR 2453 | [refactor(lct): remove unused generating functional](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2453) | Finalized ADR 0008's generic LCT boundary at normalized finite-set moments and multiplicative weights; removes unused Common/Fermionic source-functional wrappers, leaving source semantics for concrete higher-point consumers. |

| PR 2454 | [feat(transport): add normalized AHE conductivity pair](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2454) | Implements the normalized `(sxx, sxy)` pair already captured under issue #2391 in ADR 0009, reusing upstream conductivity normalization and keeping spectral broadening separate from scaling `gamma`; no separate ADR was needed. |

| 2455 | [refactor(transport): specialize generic Berry curvature to MassiveDirac](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2455) | Extended ADR 0018: specialize the generic pointwise curvature through an explicit nondegenerate spectral adapter, bridge to the projector/force-matrix and closed model formulas, and route Bastin consumers through the generic result without global-gauge claims. |

| 2456 | [refactor(transport): connect MassiveDirac ladder to generic resummation](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2456) | Extended ADR 0009: generalize ladder fixed-point/resummation over normed complex spaces, connect the MassiveDirac Pauli subspace through a faithful intertwining embedding, and derive the model solution from determinant-backed generic invertibility without geometric-series claims. |

| 2457 | [research(references): acquire missing analytic foundation sources](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2457) | Extended ADRs 0009 and 0014: map authoritative trace-per-volume, unbounded/gauge-response, and trace-class/Fredholm sources to explicit future assumptions while keeping current finite bounded response and diagonal determinant claims unchanged. |

| PR 2458 | [chore(provenance): add condensed-matter literature citations](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2458) | Adds annotated references and source provenance comments while explicitly leaving Lean declarations and behavior unchanged; its vocabulary/scope review is represented by issue-specific ADRs rather than a new architectural decision. |

| PR 2459 | [feat(transport): add scalar impurity T-matrix boundary](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2459) | Implements the model-local approximation boundary already captured under issue #2393 in ADR 0009: explicit supplied loop and invertibility, no geometric-series or exact-disorder claim. |

| PR 2460 | [refactor(imaginary-time): own timed external fields](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2460) | Extended ADR 0002: locate time-labelled fermionic field/evolution semantics in `Fermionic.ImaginaryTime`, independent of the two-point diagram representation and reusable by higher-point consumers. |

| PR 2461 | [refactor(diagrammatics): remove coupling-weight wrapper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2461) | Removes a statistics-specific alias of Common `QuarticDiagram.vertexWeight`; this is already covered by the canonical-owner/no-forwarder rule in ADR 0002. |

| PR 2462 | [refactor(twopoint): remove energy from field descriptors](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2462) | Refined ADR 0002: keep mixed-time descriptor shape/indexing independent of dispersion; require energy only when evaluating operators, shifts, commutators, or contractions. |

| PR 2463 | [feat(transport): bound scalar impurity T-matrix remainder](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2463) | Refined ADR 0009's #2393 boundary with the exact pointwise quadratic norm estimate and its explicit dependence on the supplied loop and inverse shift; it does not imply a loop-uniform or self-consistent expansion. |

| PR 2464 | [refactor(fermionic): remove unused algebraic Fock mode wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2464) | Extended ADR 0005: remove unconsumed mode-indexed aliases of basis-independent creation/annihilation; use the canonical operators directly at the representation bridge. |

| PR 2465 | [feat(diagrammatics): add generic external insertion core](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2465) | Implements the Common even-external-sector boundary already recorded under issue #1267 in ADR 0008: retain the TwoPoint API, defer bridges and connectedness predicates to consumers, and keep odd sectors outside perfect-pairing data. |

| PR 2466 | [refactor(fiber): reuse canonical shuffle slot order](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2466) | Reuses the existing left-slot order map and preserves current external/vacuum `Equiv.cast` forms; no new durable ownership or semantic boundary beyond the shuffle decisions already recorded in ADR 0008. |

| PR 2467 | [refactor(quartic): reuse Mathlib subtype equivalence](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2467) | Removes a diagram-independent equivalence wrapper in favor of Mathlib's canonical subtype equivalence while retaining semantic partner shorthands; this follows ADR 0002's canonical-owner rule without adding a new decision. |

| PR 2468 | [feat(diagrammatics): split external and vacuum components](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2468) | Implements the #1267 distinction already captured in ADR 0008: vacuum-free means every component meets an external insertion, permits multiple such components, and does not imply full external connectedness. |

| PR 2469 | [feat(transport): prove small-strength T-matrix asymptotics](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2469) | Extended ADR 0009: prove fixed-loop family-level `O(v_imp²)` through eventual invertibility and a uniform inverse bound, while leaving varying self-consistent loops and the continuum Born coefficient bridge open. |

| PR 2470 | [refactor(combinatorics): generalize sigma product reindexing](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2470) | Extended ADR 0002: place dependent-sum product reindexing in generic Combinatorics after independent pairing and TwoPoint consumers, removing only the pairing-specific proof wrapper. |

| PR 2471 | [refactor(pairing): generalize normalized-pair restriction](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2471) | Extended ADR 0008: place partner-invariant normalized-pair restriction in Combinatorics, retaining only meaningful mixed-domain wrappers in TwoPoint consumers. |

| 2472 | [refactor(linear-response): route fermionic frequency responses through ResponseChannel](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2472) | Extended ADR 0009: package measured current, source, and contact as one generic response channel for the exact two-time finite-`T` transform, without stationarity or physical-limit claims; retain the one-lag transform downstream. |

| PR 2473 | [refactor(two-point): use sigma fiber equivalence directly](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2473) | Removes a forwarding equivalence in favor of Mathlib's `Equiv.sigmaFiberEquiv` while retaining the semantic fiber type; covered by ADR 0002's canonical general-owner rule. |

| PR 2474 | [refactor(quartic): derive fixed-order pairs from component equivalence](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2474) | Reuses the canonical component pair equivalence instead of duplicating normalized-pair transport; already covered by ADR 0008's canonical pair-membership and transport decisions. |

| PR 2475 | [refactor(thermal): consolidate completed fermionic thermal modules](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2475) | Extended ADRs 0002, 0005, and 0006: organize completed thermal proofs by Gibbs, pairing/KMS, and mode-truncation responsibilities rather than proof order; retain generic pairing induction in Common and preserve theorem statements. |

| PR 2476 | [refactor(thermal): remove redundant fermionic BDD specializations](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2476) | Refined ADR 0006: retain the generic BDD theorem in Common and remove a thin Fermionic forwarder and arbitrary-weight example from the thermal umbrella; only meaningful thermal semantics stay there. |

| PR 2477 | [refactor(thermal): simplify Fin sum reindexing](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2477) | Replaces local finite-sum cast equivalences with Mathlib's `Equiv.sum_comp`; preserves recursion APIs and adds no domain-level decision beyond the canonical-general-owner policy. |

| PR 2478 | [refactor(thermal): lift finite Gibbs coordinates above BDD](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2478) | Extended ADRs 0002 and 0003: own finite Gibbs weights and trace-ratio facts upstream of BDD so perturbation/thermal consumers can reuse them without depending on pairing-specific implementation. |

| PR 2479 | [refactor(pairing): generalize ordered transport](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2479) | Extended ADR 0008: transport ordered pairings and quartic diagrams along the consumer's `Fin k ≃ S` directly, retaining relabeling as a specialization and avoiding cardinality round trips and shuffle casts. |

| PR 2480 | [refactor(pairing): index restricted pair endpoints](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2480) | Follow-up to the generic normalized-pair boundary in ADR 0008: uses one `Fin 2`-indexed endpoint theorem and removes redundant TwoPoint endpoint wrappers; no separate ADR was needed. |

| PR 2481 | [refactor(two-point): index mixed component pair endpoints](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2481) | Closed in favor of #2480; its useful endpoint indexing was carried into the generic `Fin 2` API already recorded in ADR 0008, so it adds no separate implementation or decision. |

| PR 2482 | [refactor(thermal): separate fermionic Gibbs representation layers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2482) | Extended ADRs 0005 and 0016: separate finite-coordinate Boltzmann/perturbation data from pure-point spectral summability and completed Fock Gibbs state, which specializes the generic Gibbs owner. |

| PR 2483 | [refactor(shuffle): canonicalize vacuum coordinates](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2483) | Applies ADR 0008's generalized-order transport at the shuffle boundary: standardizes vacuum coordinates directly on the known `Fin k`, removing cast/HEq helpers except for one value-level bridge. |

| PR 2484 | [refactor(thermal): internalize weighted Green-function helpers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2484) | Refined ADRs 0002 and 0006: keep one-consumer arbitrary-weight coordinate machinery private inside the physical free-Gibbs Green-function owner, while generic normalized coordinates remain in Common. |

| PR 2485 | [refactor(thermal): remove unused occupation cumulant module](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2485) | Extended ADR 0006: keep arbitrary complex-weight occupation combinatorics out of the Fermionic thermal API unless it has a real Gibbs/KMS consumer or thermal contract. |

| PR 2486 | [refactor(external-piece): preserve shuffle slot coordinates](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2486) | Applies ADR 0008's direct-order transport rule to external pieces, preserving the shuffle's native `Fin m` coordinates and eliminating downstream cast/HEq plumbing; no separate decision was needed. |

| PR 2487 | [refactor(thermal): specialize completed unbounded expectation](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2487) | Extended ADRs 0005 and 0016: derive an integrability-aware thermal API for the actual completed total-number operator, not an arbitrary diagonal operator; retain generic unbounded energy expectation in QuantumTheory. |

| PR 2488 | [refactor(berry): specialize generic curvature to MassiveDirac](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2488) | Closed as an early work-in-progress slice of #2455; its `Fin 2` spectral-index boundary is retained in the final #2530 adapter and added to ADR 0018, so no separate ADR entry was created. |

| 2489 | [refactor(analysis): isolate intrinsic/represented balance adapters](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2489) | Extended ADR 0002: keep intrinsic balance semantics independent, put represented conversions in the only adapter importing both, and share symmetric-localization algebra in a neutral owner guarded by architecture contracts. |

| 2490 | [refactor(analysis): centralize Fin-coordinate pullback for shuffle regularity](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2490) | Extended ADR 0008: share one non-injective finite-coordinate pullback theorem for local boundedness, with binary and finite-family shuffles composing their existing product combinators and retaining distinct representations. |

| 2494 | [Audit coordinatewise proofs for dimension-independent structure](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2494) | Extended ADR 0002: generalize only mathematics that is genuinely dimension-independent, reuse Mathlib first, and retain model-facing `Fin 2` formulas or short proofs when a broader adapter has no independent consumer. |

| PR 2495 | [refactor(matrix): generalize trace entry expansion](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2495) | Implements one #2494 audit candidate: the trace identity is dimension-independent but remains private because it has one consumer, so no new public matrix API was introduced. |

| PR 2496 | [refactor(ladder): use matrix continuity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2496) | Implements #2494 by delegating matrix-vector and determinant limits to Mathlib while retaining the genuinely two-dimensional MassiveDirac rotation-matrix constructor; captured in ADR 0002. |

| PR 2497 | [feat(transport): bridge T-matrix coefficient to Born self-energy](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2497) | Implements the quadratic clean-loop/Born bridge already recorded under issue #2393 in ADR 0009, keeping the mean `n_imp v_imp I`, regulator, single measure factor, and `W = n_imp v_imp²` convention explicit. |

| PR 2498 | [refactor(pauli): derive products from basis algebra](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2498) | Refined ADR 0002's #2494 record: keep the semantic three-axis Pauli type, reuse Mathlib's `Fin 3` cross product, and derive synthesized products/traces from one private indexed basis law. |

| PR 2499 | [refactor(permutation): move cycle defect parity to owner](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2499) | Implements the #2494 ownership correction: arbitrary permutation cycle-defect parity belongs in `Permutation.OrbitPartition`, while pairing-specific sign transport stays private in the pairing bridge. |

| PR 2500 | [refactor(berry): construct pointwise data from nondegenerate eigenbasis](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2500) | Closed without merge; replaced by #2501's simple-spectrum constructor. No separate ADR was added for this superseded draft. |

| PR 2501 | [feat(berry): construct simple-spectrum pointwise data](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2501) | Extended ADR 0018: derive eigenvector derivatives algebraically in the parallel-transport convention from simple-spectrum data and self-adjoint derivatives, without selecting a global model eigenvector gauge. |

| PR 2502 | [refactor(pauli): derive Hermitian structure from basis](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2502) | Refined ADR 0002's Pauli boundary: expose the axis-indexed basis once Hermitian structure gives it a second independent use, while keeping one-consumer direction routing private. |

| 2503 | [refactor(combinatorics): replace predicate-only subtype equivalences with Mathlib APIs](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2503) | Extended ADR 0002: use Mathlib for value-preserving predicate transport, but retain project equivalences that carry semantic shuffle, pairing, fiber, or block data. |

| 2504 | [refactor(permutation): use Mathlib arrow equivalence for assignment relabeling](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2504) | Reuses Mathlib's `Equiv.arrowCongr` to remove another hand-written value-preserving equivalence, consistent with ADR 0002 and #2503; the cycle-kernel semantics remain unchanged. |

| 2505 | [refactor(trace-class): reuse Mathlib unitary linear-isometry equivalence](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2505) | Replaces a local equivalence constructor with `Unitary.linearIsometryEquiv` and packages adjoint-inverse laws once; theorem semantics and trace-class scope stay unchanged, so ADR 0014 needs no new decision. |

| PR 2506 | [refactor(pauli): make the indexed basis canonical](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2506) | Extended ADR 0002: make `PauliAxis`/`pauliBasis` the algebraic owner, model combinations as finite basis sums, and retain explicit X/Y/Z coordinates only at the concrete matrix boundary. |

| PR 2507 | [refactor(permutation): generalize full-cycle characterization](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2507) | Extended ADR 0002: move arbitrary finite-permutation cycle characterization to `Permutation.OrbitPartition`; keep only the trace consumer's `Fin (n + 2)` enumeration private. |

| PR 2508 | [feat(massive-dirac): add pointwise Berry spectral data](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2508) | Supplies the MassiveDirac spectral adapter later used by #2455; its Fin 2-to-Band labeling and pointwise-only boundary are already captured in ADR 0018. |

| PR 2509 | [refactor(pairing): centralize congruence closure](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2509) | Extended ADR 0008: define disjoint-sum and dependent-sum closure on the generic pairing predicate so multiple consumers reuse one canonical construction. |

| PR 2510 | [refactor(trace-class): reuse Mathlib unitary equivalence](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2510) | Implements #2505 by reusing `Unitary.linearIsometryEquiv`; already recorded with the issue and no new operator-ideal boundary. |

| PR 2511 | [refactor(combinatorics): reuse Mathlib subtype equivalences](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2511) | Implements issue #2503's predicate-only subtype transport rule already recorded in ADR 0002. |

| PR 2512 | [feat(massive-dirac): bridge projectors to Berry eigenbasis](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2512) | Intermediate #2455 bridge identifying model band projectors with rank-one projectors from generic spectral data; included in ADR 0018's final specialization boundary. |

| PR 2513 | [refactor(permutation): use Mathlib arrow equivalence](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2513) | Implements issue #2504's wrapper removal using `Equiv.arrowCongr`, already covered by ADR 0002's canonical-general-equivalence rule. |

| PR 2514 | [feat(massive-dirac): bridge force numerator to Berry matrix elements](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2514) | Completes an intermediate #2455 step by aligning projector-force numerators with generic Hamiltonian-derivative matrix elements; included in ADR 0018's final specialization bridge. |

| PR 2515 | [refactor(analysis): isolate balance law adapters](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2515) | Implements the intrinsic/represented dependency split from #2489: the adapter owns conversion, and shared symmetric-localization algebra stays representation-neutral, as recorded in ADR 0002. |

| PR 2516 | [refactor(linear-response): route finite frequency response through channel](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2516) | Implements #2472's representation-independent finite-time response channel and Fermionic current/contact adapter; already reflected in ADR 0009. |

| PR 2517 | [docs(operator): fix Gibbs heat boundary](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2517) | Added the heat-operator-first boundary for infinite-dimensional Gibbs states, the upstream Hamiltonian-to-heat obligation, and pure-point compatibility by basis action; integrated into ADRs 0011, 0013, and 0016. |

| PR 2518 | [refactor(density): centralize positive normalization](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2518) | Made positive spectral-trace-class normalization generic in `DensityOperator`; bounded Gibbs construction derives nonzero trace from compactness and a nontrivial space instead of passing `hZ` through consumers. Integrated into ADRs 0003 and 0016. |

| PR 2519 | [refactor(diagrammatics): trim mixed proof routing](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2519) | Removes one-consumer proof-routing declarations in favor of private helpers and the canonical component/leg theorems; ADR 0008 already states this public-API rule, so no new decision was needed. |

| PR 2520 | [refactor(diagrammatics): trim slot-split proof APIs](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2520) | Keeps cross-module semantic endpoints public while deleting dead routing wrappers and privatizing reused proof machinery; already covered by ADR 0008's API boundary. |

| PR 2521 | [fix(massive-dirac): adapt Berry pointwise proofs to Lean 4.33](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2521) | Toolchain-proof adjustment with unchanged Berry adapter, statements, and model semantics; no ADR change. |

| PR 2522 | [refactor(diagrammatics): remove unused two-point ordering layer](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2522) | Deletes an ordering chain with no consumer, its umbrella routing, and an unused wrapper; this applies ADR 0008's rule against semantic-free proof-stage subsystems and compatibility routes. |

| PR 2523 | [feat(gibbs): bridge heat data to pure-point states](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2523) | Uses heat basis action plus spectral-trace-class data to derive pure-point Boltzmann summability, partition equality, and normalized-state equality without a duplicate summability premise or heat-state wrapper; integrated into ADRs 0013 and 0016. |

| PR 2524 | [refactor(diagrammatics): trim two-point component APIs](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2524) | Keeps semantic connectivity/decomposition endpoints while inlining one-use proof routes and deleting unused convenience theorems, applying ADR 0008's existing API boundary. |

| Issue 2525 | [refactor(operator): give Hilbert-basis diagonal operators a neutral owner](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2525) | Moves diagonal rank-one series, basis action, compactness, and positivity into neutral `Analysis.Operator.Diagonal`; trace-class/Fredholm layers consume it as adapters, while Common's distinct diagonal representation stays separate. Recorded in ADR 0014. |

| Issue 2526 | [refactor(operator): move finite-dimensional trace out of QuantumTheory.Transport](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2526) | Moves generic finite-dimensional trace laws to `Analysis.Operator.FiniteTrace`; Streda/Massive-Dirac traced kernels remain downstream. Recorded in ADR 0002. |

| Issue 2527 | [refactor(unbounded): deepen the public Stone-evolution module](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2527) | Establishes one public Stone-evolution route while keeping resolvent/limit proofs behind it; preserves explicit domain and generator laws and makes no functional-calculus claim. Recorded in ADR 0002. |

| Issue 2528 | [refactor(operator): separate Berry geometry from the spectral operator route](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2528) | Gives finite parameter-dependent Berry geometry a dedicated public route; keeps generic eigenvector and resolvent APIs independent, while the broad operator umbrella may expose both. Recorded in ADR 0018. |

| PR 2529 | [refactor(transport): connect MassiveDirac ladder resummation](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2529) | Implements the #2456 generic normed-space fixed point, faithful Pauli embedding, and determinant-to-`IsUnit` bridge; non-crossing scope and no-geometric-series boundary are already in ADR 0009. |

| PR 2530 | [refactor(transport): specialize generic Berry curvature to MassiveDirac](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2530) | Completes #2455's pointwise model specialization and routes Bastin consumers through generic curvature; ADR 0018 already records the bridge and global-topology boundary. |

| PR 2531 | [docs(transport): add spin Hall roadmap and provenance](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2531) | Distinguishes conventional symmetrized spin current from torque-dipole proper current and separates bulk response, boundary accumulation, and device conversion; integrated into ADR 0009. |

| Issue 2532 | [roadmap(spin-hall): formalize Rashba response, disorder vertices, and spin-current reciprocity](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2532) | Requires explicit flow/spin indices and separate APIs for bare/dressed currents, edge accumulation, and device angle; open work remains distinct from current response results. Recorded in ADR 0009. |

| Issue 2533 | [research(spin-hall): fill side-jump and edge-transport provenance gaps](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2533) | Keeps side-jump/skew, disorder dependence, finite/infinite sample behavior, and edge accumulation as model/provenance work; current ADR 0009 records the scope boundary, while source-verification work remains open. |

| Issue 2534 | [refactor(transport): move 2D momentum measure out of generic Core](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2534) | Keeps `Transport.Core` dimension-independent and gives the two-dimensional physical-momentum measure one opt-in continuum owner; current prefactors and formulas remain unchanged. Recorded in ADR 0009. |

| Issue 2535 | [refactor(transport): separate finite conductivity evaluation from generic Core](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2535) | Keeps finite Lehmann response generic; the conductivity adapter alone adds contact and positive-volume electric-field normalization. Recorded in ADR 0009. |

| Issue 2536 | [refactor(transport): move pure-point spectral bridge out of generic Resolvent](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2536) | Keeps signed-regulator resolvent action generic and places `PurePointLehmannData` basis bridges in the shared Kubo–Bastin/Středa adapter. Recorded in ADR 0009. |

| PR 2537 | [refactor(transport): connect MassiveDirac ladder resummation](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2537) | Completes #2456 with the canonical Pauli embedding and Born-Dyson bridge; ADR 0009 already records the generic fixed-point, determinant, and no-convergence boundaries. |

| PR 2538 | [refactor(operator): give Hilbert-basis diagonal operators a neutral owner](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2538) | Implements #2525: neutral Analysis owns the diagonal series and compactness; positivity/spectral-trace remain TraceClass adapters. ADR 0014 now links the implementation. |

| PR 2539 | [refactor(unbounded): add public Stone evolution route](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2539) | Implements #2527 with `Analysis.Operator.Unbounded.StoneEvolution` as the public route and moves the continuum consumer off the proof-stage chain; ADR 0002 links the route. |

| PR 2540 | [feat(gibbs): prove pure-point entropy identity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2540) | Derives finite pure-point entropy and Helmholtz identity from diagonal Gibbs data plus explicit energy integrability; avoids bounded-observable coercion or a parallel state abstraction. Integrated into ADR 0016. |

| PR 2541 | [refactor(operator): move finite-dimensional trace out of QuantumTheory.Transport](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2541) | Implements #2526 by moving the generic trace laws to `Analysis.Operator.FiniteTrace` without compatibility aliases; ADR 0002 links the implementation. |

| PR 2542 | [refactor(transport): split pure-point spectral bridge](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2542) | Implements #2536 with generic signed-regulator spectral action and a shared `Transport.Spectral.PurePoint` adapter; ADR 0009 now links the closure PR. |

| PR 2543 | [docs(operator): characterize Gibbs variational boundary](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2543) | Separates bounded noncommuting variational/uniqueness proofs from countable diagonal competitors with explicit energy integrability; a full unbounded quantum extension still needs domain/relative-entropy foundations. Integrated into ADR 0016. |

| PR 2544 | [feat(gibbs): add pure-point variational principle](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2544) | Implements the diagonal/classical slice from #2543 with each countable competitor carrying normalization, entropy, and absolute energy integrability; no unbounded noncommuting principle is implied. ADR 0016 links it. |

| PR 2545 | [refactor(transport): move 2D momentum measure out of Core](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2545) | Implements #2534: removes the fixed 2D measure from `Transport.Core` and leaves the formula at the opt-in continuum owner; ADR 0009 links the PR. |

| PR 2546 | [refactor(gibbs): centralize countable entropy bound](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2546) | Shares scalar Gibbs comparison below bounded operator equality, moves generic summation order to Analysis, and derives pure-point entropy without a redundant field. Integrated into ADR 0016. |

| PR 2547 | [refactor(massive-dirac): trim redundant Berry wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2547) | Removes single-use upper/lower and reversed-curvature wrappers, leaving specializations derived from the canonical generic-to-model bridge; ADR 0018 now records this refinement. |

| PR 2548 | [feat(gibbs): characterize pure-point minimizer](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2548) | Completes the diagonal/classical variational slice: the admissible normalized Gibbs probabilities attain the lower bound and are its unique equality case; the noncommuting unbounded problem remains separate. ADR 0016 links it. |

| PR 2549 | [refactor(massive-dirac): remove unused ladder forwarder](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2549) | Removes a one-consumer Pauli-operator equality wrapper while retaining the generic coefficient theorem and Středa endpoint; ADR 0009 now records the public API boundary. |

| PR 2550 | [refactor(massive-dirac): trim stale ladder import](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2550) | Removes an accidental transitive model import and adds it at the Pauli consumer; no theorem or design change beyond explicit ownership/import boundaries already recorded. |

| PR 2551 | [refactor(massive-dirac): inline ladder resummation specialization](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2551) | Removes a one-consumer solved-vector forwarder and keeps Středa on the canonical coefficient-space theorem; ADR 0009 captures the API boundary. |

| Issue 2552 | [research(analysis): design unbounded self-adjoint functional calculus for heat evolution](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2552) | Keeps `exp (-β H)` behind justified bounded functional calculus/heat-semigroup construction with explicit domain and lower-bound data; no formal unbounded power series or trace-class claim. Open research, recorded in ADR 0011. |

| Issue 2553 | [feat(analysis): construct heat operators from semibounded self-adjoint Hamiltonians](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2553) | Places the future Hamiltonian-to-heat producer in domain-aware Analysis, feeding the existing positive heat-state normalization; remains blocked by #2552 and excludes trace-class claims. Recorded in ADRs 0011 and 0016. |

| Issue 2554 | [research(analysis): derive trace-class heat criteria from compact resolvent](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2554) | Requires proving heat compactness and Boltzmann eigenvalue summability before the existing `SpectralTraceClass` Gibbs boundary; blocked by #2552/#2553 and does not imply a general trace-class ideal. Recorded in ADRs 0013 and 0016. |

| Issue 2555 | [Architecture: consolidate statistics-independent second-quantization concepts](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2555) | Coordination umbrella for #2556 and #2557; it assigns implementation decisions to the child issues and preserves statistics-specific boundaries, so no separate ADR change. |

| Issue 2556 | [SecondQuantization.Common: own the statistics-independent total particle-number grade](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2556) | Gives finite-support occupation bases one arbitrary-mode total grade in Common, with fermionic cardinality and bosonic sum adapters; concrete configs and transition laws stay separate. Recorded in ADR 0005. |

| Issue 2557 | [Share the formal free grand-partition series backend between Bose and Fermi layers](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2557) | Gives Bose/Fermi free product, log, and connected-cycle identities one formal Gibbs owner restricted to `ζ = ±1`; determinant and analytic convergence remain statistics-specific, and no `t = 1` evaluation is implied. Recorded in ADR 0008. |

| Issue 2558 | [refactor(operator): narrow the generic Analysis.Operator route](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2558) | Keeps the public umbrella generic and makes real-line/1D realizations explicit opt-in imports at their current owners. Recorded in ADR 0002. |

| PR 2559 | [refactor: trim redundant theorem wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2559) | Removes two one-consumer proof-route wrappers and uses Mathlib's canonical commutator theorem directly; ADR 0002 already states the general ownership and no-forwarder rule. |

| PR 2560 | [refactor: centralize particle-number grade](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2560) | Implements #2556: Common owns the arbitrary-mode total grade; Bose/Fermi adapters retain native configuration forms and stat-specific transitions. ADR 0005 links the implementation. |

| PR 2561 | [refactor(thermal): share free grand-series backend](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2561) | Implements #2557 with a `ζ = ±1` Gibbs backend, retaining Bose/Fermi endpoints and removing unused intermediate log wrappers; no `t = 1` or convergence claim. ADR 0008 links it. |

| PR 2562 | [refactor(transport): separate finite conductivity adapter](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2562) | Implements #2535 by moving the contact/positive-volume evaluator from Core to `Transport.FiniteConductivityTable`; formula, theorem values, and names stay unchanged. ADR 0009 links it. |

| PR 2563 | [refactor(pauli): lift coefficient uniqueness to linear independence](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2563) | Promotes generic indexed Pauli-basis linear independence to Analysis while keeping MassiveDirac subset-independence and injectivity facts local; recorded in ADR 0002. |

| PR 2564 | [feat(diagrammatics): restrict generic vacuum components](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2564) | Adds a first higher-point restriction slice: vacuum components become quartic diagrams via generic partner-invariant pairing restriction; external-bearing components and crossing-sign transport remain unproved. Recorded in ADR 0008. |

| PR 2565 | [chore(ci): streamline audited workflows](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2565) | Separates source-topology and compiled-build triggers, keeps theorem-catalog work advisory on PRs, and makes routine source/umbrella boundaries declarative; recorded in ADRs 0010 and 0020. |

| PR 2566 | [refactor(pairing): generalize fixed-point-free involutions](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2566) | Makes arbitrary-type pairing and invariant-subtype restriction generic in `PairingOn`; finite ordering, normalized pairs, and crossings remain on `Pairing n`. Recorded in ADR 0008. |

| PR 2567 | [refactor(ci): narrow diagrammatics architecture checks](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2567) | Stops freezing retired stage directories and flat module paths; keeps dependency direction and narrow exact-public-endpoint import guards. Recorded in ADR 0010. |

| PR 2568 | [feat(diagrammatics): expose external component sector](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2568) | Closed without a merged diff; its design isolates the component-local external subset and even-cardinality proof as prerequisites to local `Fin (2 * E')` reindexing. No separate ADR change; the external-bearing restriction boundary is already captured in ADR 0008, with later implementation history reviewed in sequence. |

| PR 2569 | [refactor(combinatorics): generalize equivalence coordinate changes](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2569) | Gives shared-source equivalences one generic target-coordinate change API and removes the shuffle-only relative permutation; recorded in ADR 0002. |

| PR 2570 | [feat(diagrammatics): expose external component sector](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2570) | Adds generic `PairingOn.even_card`; Common extracts each component's external sector and proves it even, while explicit local reindexing remains the next stage. Recorded in ADR 0008. |

| PR 2571 | [feat(diagrammatics): reindex external component sector](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2571) | Defines the local external-pair count and an increasing order isomorphism into the ambient external subset, preserving insertion order for later sign transport. Recorded in ADR 0008. |

| PR 2572 | [refactor(pairing): keep combinators at bundle level](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2572) | Adds canonical `PairingOn` invariant, sum, dependent-sum, and transport APIs so consumers compose bundled pairings instead of rebuilding involution proofs; reinforces ADR 0008. |

| PR 2573 | [feat(diagrammatics): restrict external components](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2573) | Builds `restrictComponent` for every connected component by composing external-order reindexing, interaction-sector extraction, and `PairingOn.restrictAlongEquiv`; keeps its one-use leg equivalence private and the vacuum-to-quartic route separate. Recorded in ADR 0008. |

| PR 2574 | [refactor(diagrammatics): fix external insertion leg order](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2574) | Replaces arbitrary leg enumeration with external-first, then increasing interaction-vertex/local-leg order, establishing the ordered basis for later crossing/sign transport. Recorded in ADR 0008. |

| PR 2575 | [feat(diagrammatics): transport external component pairing](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2575) | Exposes the semantic local-to-ambient leg embedding and pairing-partner transport law while keeping the construction-only subtype equivalence private. Recorded in ADR 0008. |

| PR 2576 | [refactor(diagrammatics): audit fermionic two-point stack](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2576) | Moves the diagram-independent timed-field Gibbs contraction into Fermionic Thermal; two-point and quartic consumers share it, while one-use regularity/proof-routing modules are removed or privatized. Recorded in ADR 0002. |

| PR 2577 | [feat(diagrammatics): order external component legs](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2577) | Proves the local-to-ambient leg map is an order embedding and uses the canonical normalized-pair embedding to preserve and reflect crossings. Recorded in ADR 0008. |

| PR 2578 | [feat(diagrammatics): decompose external component pairs](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2578) | Reconstructs a private global leg equivalence and exposes the equivalence between the dependent sum of component-local normalized pairs and ambient normalized pairs; inter-component crossing terms remain explicit. Recorded in ADR 0008. |

| PR 2579 | [refactor(diagrammatics): centralize quartic leg semantics](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2579) | Moves flattened quartic-leg field/operator semantics upstream from Wick/Dyson consumers and separates the operator-product identity; two-point semantics no longer imports Dyson flattening. Recorded in ADR 0002. |

| Issue 2580 | [Formalize replica-method proof of the linked-cluster theorem](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2580) | Establishes a formal replica-count polynomial cross-check independent of Möbius/cumulant inversion; no analytic `n → 0` limit. The generic bridge and Fermionic specialization are implemented by PRs #2582, #2622, and #2626, with the dependency firewall audited in #2628. Recorded in ADR 0008. |

| PR 2581 | [docs(linked-cluster): plan replica-method proof track](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2581) | Records the formal replica polynomial and inversion-independent dependency firewall in the roadmap; the durable decision is captured under parent issue #2580 in ADR 0008. |

| PR 2582 | [feat(cumulant): add replica-count polynomial](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2582) | Adds the finite-set replica polynomial and linear-coefficient theorem in Combinatorics, using forward `Moment` only and no inversion layer; implementation of issue #2580, already recorded in ADR 0008. |

| PR 2583 | [feat(diagrammatics): decompose external component crossings](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2583) | Gives an exact local-plus-intercomponent crossing count and residual exchange-weight factorization; keeps intercomponent crossings explicit rather than assuming quartic parity cancellation. Recorded in ADR 0008. |

| PR 2584 | [feat(power-series): add replica-count polynomial](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2584) | Defines a finite falling-factorial replica polynomial at each perturbation order and proves its natural-number evaluations equal normalized coefficients of `Z ^ n`; no analytic continuation. Adds detail to ADR 0008's issue #2580 record. |

| PR 2585 | [refactor(thermal): use canonical list operator product](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2585) | Replaces generic composed-list wrappers with `List.prod` for endomorphisms; retains semantic Bosonic ordered-product APIs as thin standard-library implementations. Recorded in ADR 0002. |

| PR 2586 | [refactor(operator): move finite exchange peel upstream](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2586) | Moves generic scalar exchange peeling to Analysis, keeps ζ-commutator algebra separate, and leaves Bosonic `exchangeValue` as an ordering coefficient rather than a thermal contraction. Recorded in ADR 0002. |

| PR 2587 | [feat(diagrammatics): relate external crossings to leg inversions](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2587) | Relates the parity of the two oriented crossings for a component pair to the inversion parity of their ambient leg embeddings; leaves component ordering to the actual shuffle/time-order consumer. Recorded in ADR 0008. |

| PR 2588 | [feat(power-series): prove replica log coefficient identity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2588) | Proves the coefficient linear in the formal replica variable equals the factorial-normalized formal-log coefficient, using falling factorials and no inversion endpoint. Adds detail to ADR 0008's issue #2580 record. |

| PR 2589 | [feat(diagrammatics): expose external component leg shuffle](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2589) | Packages component leg embeddings as `FamilySlotShuffleTo` and reuses the generic oriented inter-block inversion count without choosing an order for component indices. Recorded in ADR 0008. |

| PR 2590 | [refactor(operator): narrow generic route](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2590) | Implements #2558 by removing concrete real-line/1D specializations from the generic Analysis.Operator umbrella; consumers keep explicit leaf imports. ADR 0002 already records this boundary; no additional decision was needed. |

| PR 2591 | [refactor(diagrammatics): fold quartic reassembly laws into owner](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2591) | Folds reassembly inverse laws into the `QuarticDiagram.reassemble` owner and removes the one-consumer routing module; ADR 0008 already states this rule, so no new architecture change. |

| PR 2592 | [feat(cumulant): interpret replica polynomial by colorings](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2592) | Gives natural replica-count evaluation its block-coloring meaning and keeps that semantics on the replica polynomial rather than adding a wrapper; detail for issue #2580, already captured in ADR 0008. |

| PR 2593 | [refactor(quartic): generalize local-leg exchange API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2593) | Moves the exchange law from vertex/index coordinates onto the semantic `QuarticLocalLeg` type and removes the old specialization. Recorded in ADR 0002. |

| PR 2594 | [feat(diagrammatics): sum external component crossing parity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2594) | Generalizes off-diagonal pair congruence summation and equates residual crossing parity with ordered block-inversion parity for an explicit component order. Recorded in ADR 0008. |

| PR 2595 | [refactor(diagrammatics): canonicalize interaction sector](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2595) | Closed without merge; proposes one Common/Diagrammatics owner for the interaction sector instead of family-specific definitions. The current source history shows the canonical API landed later in #2599; defer the ADR update to that merged implementation. |

| PR 2596 | [refactor(quartic): generalize local-leg evolution](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2596) | Moves Heisenberg evolution onto the semantic `QuarticLocalLeg`; model-specific APIs are derived from it, and the Dyson-only dressed-leg theorem is replaced by the canonical TimedField bridge. Recorded in ADR 0002. |

| PR 2597 | [feat(cumulant): expand replica polynomial in falling factorials](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2597) | Converts the finite-set replica polynomial into the falling-factorial basis used by the power-series replica polynomial, keeping basis-conversion helpers private. Detail for issue #2580, already recorded in ADR 0008. |

| PR 2598 | [refactor(quartic): remove evolution specialization chain](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2598) | Deletes single-consumer evolution wrappers and performs the finite interaction specialization locally, while retaining an independently meaningful vertex-level eigenoperator theorem with a recorded rationale. Recorded in ADR 0020. |

| PR 2599 | [refactor(diagrammatics): canonicalize interaction sector](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2599) | Moves the shared interaction-sector extraction to Common/Diagrammatics and removes duplicated TwoPoint/ExternalInsertion APIs while preserving the filtered ambient-vertex form. Records the landed replacement for stacked #2595 in ADR 0008. |

| PR 2600 | [refactor(quartic): generalize local-leg field bridge](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2600) | Makes the external-field label plus bare-operator, energy-shift, and timed-field bridges accept `Common.QuarticLocalLeg` directly; flattened and two-point consumers decode coordinates at their boundary. Recorded in ADR 0002. |

| PR 2601 | [refactor(cumulant): move forward refinement lemmas](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2601) | Moves partition-product refinement identities from Möbius inversion to the forward moment layer, removing an unnecessary inversion dependency for the replica bridge. Recorded in ADR 0008. |

| PR 2602 | [refactor(set-partition): separate coarsening from Mobius](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2602) | Keeps coarsening/order-isomorphism structure independent of incidence algebra and moves the Möbius identity to the dedicated SetPartition/Mobius layer. Recorded in ADR 0008. |

| PR 2603 | [feat(diagrammatics): expose component external shuffle](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2603) | Exposes the canonical external-only component shuffle in Common by reusing each component's increasing external order isomorphism; leaves sign interpretation downstream. Recorded in ADR 0008. |

| PR 2604 | [refactor(diagrammatics): centralize external component semantics](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2604) | Centralizes external/vacuum classification for graphs on `External ⊕ Internal`, removes family-specific component-partition wrappers, and leaves TwoPoint-specific connectivity facts local. Recorded in ADR 0008. |

| PR 2605 | [refactor(quartic): remove local-leg evolution wrapper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2605) | Removes a one-consumer vertex/index specialization of the Common local-leg evolution law while preserving the meaningful flattened-sequence API, which now specializes the Common theorem directly. Recorded in ADR 0002. |

| PR 2606 | [refactor(quartic): remove bosonic local-leg evolution wrapper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2606) | Removes the unused Bosonic specialization and its now-unneeded imports, completing the removal of duplicate one-use local-leg evolution wrappers from both statistics layers. Recorded in ADR 0002. |

| PR 2607 | [feat(set-partition): count blocks by Stirling numbers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2607) | Closed without merge. Its Stirling enumeration proposal was later landed in #2610 after resolving the SetPartition/Cumulant dependency and public-routing concerns; defer ADR evidence to that merged PR. |

| PR 2608 | [docs(conventions): require iterative review](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2608) | Adds an implementation review/fix loop to `notes/conventions.md`. This is a development-process convention rather than a repository architecture decision, so no ADR change. |

| PR 2609 | [refactor(set-partition): decouple distinguished blocks from cumulants](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2609) | Makes the distinguished-block API structural, moves only the moment-specific factorization to `Cumulant.Moment`, and preserves the public moment theorem statement. Recorded in ADR 0008. |

| PR 2610 | [feat(set-partition): count blocks by Stirling numbers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2610) | Supersedes unmerged #2607: adds the pure set-partition block-count theorem, hides the convolution proof, and exports the result through `Combinatorics.SetPartition`. Recorded in ADR 0008. |

| PR 2611 | [refactor(perfect-pairing): narrow decomposition imports](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2611) | Uses leaf imports inside the pairing package, re-exports decomposition modules from the public umbrella, and keeps higher-level recursion explicit. Recorded in ADRs 0002 and 0010. |

| PR 2612 | [feat(combinatorics): transport family shuffle parity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2612) | Adds a generic theorem transporting pointwise off-diagonal inversion congruences to the total ordered parity for a supplied block order, with no equal-size or diagrammatics dependency. Recorded in ADR 0008. |

| Issue 2613 | [prove partition Möbius formula without power-series dependency](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2613) | Resolved by merged PR #2616: replaces the formal-power-series derivation with an integer-valued finite moment/cumulant inversion argument for the same Möbius formula. Recorded in ADR 0008. |

| PR 2614 | [docs(combinatorics): refresh roadmap module paths](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2614) | Refreshes the combinatorics roadmap to current module paths and ownership splits. Documentation now aligned with ADR 0008; no new decision beyond the existing ownership boundary. |

| PR 2615 | [feat(diagrammatics): reduce component shuffle parity to externals](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2615) | Proves that full component-leg interleaving parity reduces to the external-only shuffle modulo two, using four-leg interaction blocks and the generic parity-transport theorem. Recorded in ADR 0008. |

| PR 2616 | [refactor(set-partition): prove Mobius formula combinatorially](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2616) | Resolves #2613 by replacing the formal-log specialization with a finite moment/cumulant inversion proof, preserving the public Möbius formula statements. Recorded in ADR 0008. |

| PR 2617 | [refactor(set-partition): narrow Stirling imports](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2617) | Removes an unused equivalence import and broad tactic umbrella after review of #2610; theorem statements and proofs are unchanged, so no ADR change. |

| PR 2618 | [refactor(set-partition): narrow Stirling imports](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2618) | Closed without merge after its import-only review. #2617 had already landed the corresponding Stirling import cleanup; no architectural decision or ADR change. |

| PR 2619 | [refactor(combinatorics): narrow tactic imports](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2619) | Replaces remaining broad tactic umbrellas in two combinatorics modules with the specific tactic imports they use; statements and proofs are unchanged, so no ADR change. |

| PR 2620 | [feat(replica): count fixed-block coarsenings](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2620) | Counts fixed-block coarsenings by Stirling numbers and reindexes the forward moment sum over outer partitions into fine partitions with multiplicity, without cumulant or connected-decomposition inversion. Recorded in ADR 0008. |

| PR 2621 | [feat(diagrammatics): identify fermionic external component sign](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2621) | Adds a Fermionic external-insertion API: with caller-supplied component order, residual inter-component pairing weight is the external shuffle sign and full weight factors into that sign and local weights. Time-order representation remains downstream. Recorded in ADR 0008. |

| PR 2622 | [feat(replica): prove power-series replica bridge](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2622) | Completes the forward replica bridge between finite-set and power-series polynomials and the formal linked-cluster endpoint by linear coefficient extraction, without cumulant inversion or analytic replica limits. Recorded in ADR 0008. |

| PR 2623 | [refactor(perfect-pairing): inline restriction endpoint helper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2623) | Removes a one-use public helper and inlines the short proof into the generic normalized-pair restriction equivalence, leaving the consumer-facing restriction API unchanged. Recorded in ADR 0002. |

| PR 2624 | [feat(diagrammatics): expose component interaction shuffle](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2624) | Exposes the canonical interaction-only component shuffle and proves component interaction sectors sum to the ambient vertex count, supplying downstream ordered-simplex indexing. Recorded in ADR 0008. |

| PR 2625 | [feat(combinatorics): decompose finite family orders](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2625) | Decomposes a global finite order into local fiber orders and a family shuffle, retaining empty fibers as zero-size blocks with an extraction/reassembly equivalence. Recorded in ADR 0008. |

| PR 2626 | [feat(replica): specialize fermionic linked-cluster theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2626) | Routes the existing finite-mode Fermionic linked-cluster theorem through the generic replica endpoint, preserving its public statement and avoiding transitive inversion-based power-series cumulant dependencies. Recorded in ADR 0008. |

| PR 2627 | [feat(diagrammatics): decompose external interaction orders](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2627) | Equates global interaction-vertex orders with local component orders plus a shuffle, retaining zero-vertex components as empty orders and zero-size blocks. Recorded in ADR 0008. |

| PR 2628 | [chore(replica): audit linked-cluster proof independence](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2628) | Adds an architecture source-topology rule forbidding the generic replica bridge and Fermionic specialization from depending on inversion/cumulant endpoints; updates proof-route status documentation. Recorded in ADRs 0008, 0010, and 0020. |

| PR 2629 | [refactor(operator): separate Berry geometry route](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2629) | Moves finite-dimensional pointwise Berry connection/curvature to a dedicated public route, keeps spectral eigenvector/resolvent infrastructure independent, and preserves declarations through the umbrella. Recorded in ADR 0018. |

| PR 2630 | [refactor(perfect-pairing): canonicalize pairing transport](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2630) | Replaces permutation-only relabeling with the general pairing transport API, removing duplicate constructors/lemmas and migrating consumers without aliases. Recorded in ADR 0008. |

| PR 2631 | [docs(readme): simplify repository overview](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2631) | Keeps the README to purpose, primary documentation links, badges, and build command; delegates changing theorem inventories to the Explorer and project notes. Documentation-surface cleanup, no ADR change. |

| PR 2632 | [refactor(transport): split occupation analysis ownership](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2632) | Separates arbitrary band occupation, pointwise zero-temperature step, band-filling predicates, and Lorentzian edge analysis; preserves the strict endpoint and migrates model imports to narrow owners. Recorded in ADR 0009. |

| PR 2633 | [refactor(perfect-pairing): inline zero off-diagonal specialization](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2633) | Replaces a one-use zero-target wrapper with the general off-diagonal sum congruence directly; the general theorem and diagonal congruence remain. Recorded in ADR 0008. |

| PR 2634 | [feat(analysis): factor finite-family ordered-simplex order sums](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2634) | Adds the generic ordered-simplex sum/product theorem under a shuffled pointwise integrand factorization and local measurability/boundedness, leaving domain-specific factorization downstream. Recorded in ADR 0008. |

| PR 2635 | [refactor(perfect-pairing): reuse restriction for erase zero](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2635) | Deletes erase-zero-specific restricted-partner machinery and builds through generic `PairingOn.restrictAlongEquiv`, keeping only the deletion-specific invariant-subtype proof local. Recorded in ADR 0008. |

| PR 2636 | [refactor(linear-response): centralize Lehmann transition data](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2636) | Centralizes gap/weight/phase/frequency data in `LehmannTransitionData hbar`, adapts operator and finite-table representations, and preserves public finite response statements. Recorded in ADR 0009. |

| PR 2637 | [refactor(perfect-pairing): inline IsPairing construction proofs](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2637) | Removes three one-use public proof-routing helpers and inlines their involution proofs into the bundled `PairingOn` constructors. Covered by the same public-surface principle as #2623 in ADR 0008; no separate decision. |

| PR 2638 | [docs(combinatorics): refresh Mobius formula status](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2638) | Removes the stale roadmap description after #2616 completed the finite proof. Confirms ADR 0008's current ownership statement; no additional architecture decision. |

| PR 2639 | [refactor(perfect-pairing): inline endpoint inverse](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2639) | Removes a named inverse helper that duplicated `pairEndpointEquiv.symm`, migrates consumers to the canonical equivalence inverse, and preserves consumer APIs. Covered by the pairing public-surface rule in ADR 0008; no separate decision. |

| PR 2640 | [feat(diagrammatics): factor external insertion vertex weights](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2640) | Adds a generic interaction-vertex weight over a commutative monoid and factors it together with the Dyson sign over components, preserving empty interaction sectors as neutral factors. Recorded in ADR 0008. |

| PR 2641 | [refactor(perfect-pairing): remove unused evaluation lemmas](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2641) | Removes two unconsumed evaluation corollaries while retaining `Pairing.evaluation`; this is a reviewed API cleanup, consistent with ADR 0020's rule that terminality triggers review rather than automatic deletion. No new decision. |

| Issue 2642 | [keep one-dimensional weak conservation out of the generic calculus route](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2642) | Open proposal to make concrete 1D weak-conservation imports opt-in while retaining their Analysis ownership. No implementation or accepted outcome yet, so no ADR change. |

| PR 2643 | [docs(combinatorics): retain right split closure theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2643) | Records why `Pairing.isSplit_inr` remains public: it captures the involution-derived right-closure fact independently of its current constructor consumer. Recorded in ADR 0020. |

| PR 2644 | [refactor(perfect-pairing): inline embedding projection](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2644) | Inlines a definitional `rfl` projection used once inside the module while retaining the canonical embedding and independent membership/crossing APIs. Covered by the pairing API-surface principle in ADR 0008; no separate decision. |

| PR 2645 | [Refactor mixed component crossing parity through generic theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2645) | Reuses the generic pairing component-crossing parity theorem, deletes duplicated two-point crossing machinery, and keeps only the four-leg vacuum parity argument local. Applies ADR 0008's existing ownership boundary; no new API. |

| PR 2646 | [Factor interaction-sector component decomposition](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2646) | Adds the generic ambient-to-component interaction-sector equivalence, removes TwoPoint and ExternalInsertion duplicates, and reuses it for shuffles, orders, and vertex products. Recorded in ADR 0008. |

| PR 2647 | [refactor(perfect-pairing): remove unused core helpers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2647) | Removes unconsumed helpers that only restated structure fields, trivial universe membership, or an existing theorem, while keeping canonical pairing and endpoint APIs. Recorded in ADR 0020 with the retain/delete distinction. |

| PR 2648 | [Privatize external-insertion partner-invariance helper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2648) | Makes a same-module-only helper private while retaining TwoPoint/Quartic analogues that have downstream consumers. Recorded in ADR 0008. |

| PR 2649 | [refactor(perfect-pairing): narrow insert-first-pair API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2649) | Removes/privateizes local proof helpers but keeps the erase/insert round trips and `equivSigma` public as the mathematical recursion API. Recorded in ADR 0008. |

| PR 2650 | [refactor(bdd): name generic theorem after Bloch-de Dominicis](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2650) | Renames a generic expectation expansion to its canonical mathematical identity, migrates consumers and ownership checks, and leaves representation adapters unchanged. Recorded in ADR 0006. |

| PR 2651 | [refactor(fermionic-thermal): derive occupation from BDD](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2651) | Derives the number-operator occupation from the canonical BDD two-point API using the energy shift, CAR, and non-resonance, removing duplicate powerset/weighted-trace calculations. Recorded in ADR 0006. |

| PR 2652 | [Remove unused external-insertion interaction shuffle API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2652) | Removes an unused standalone slot shuffle, projection theorem, and its sole-consumer cardinality lemma, while preserving the generic component equivalence and full interaction-order decomposition. Recorded in ADR 0008. |

| PR 2653 | [refactor(perfect-pairing): narrow crossing parity API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2653) | Removes or privatizes proof-only parity helpers while preserving the externally used crossing, inversion, off-diagonal, and finite-type APIs. Applies ADR 0008's existing public-surface boundary; no new decision. |

| PR 2654 | [refactor(perfect-pairing): use generic crossing transport](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2654) | Replaces a same-module erase-zero crossing wrapper with `crosses_map_iff` and its strict-order embedding, keeping the recursive crossing-count API unchanged. Covered by ADR 0008's generic crossing boundary. |

| PR 2655 | [docs(combinatorics): retain pairing audit endpoints](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2655) | Records pairing cardinality, permutation-sign, and erase/insert round-trip declarations as intentionally retained because each is a canonical mathematical/API endpoint despite low consumer counts. Recorded in ADR 0020. |

| PR 2656 | [refactor(perfect-pairing): remove unused transport equivalence](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2656) | Removes a zero-consumer equivalence wrapper around `PairingOn.transport`, preserving the canonical operation and its round-trip/composition laws. Recorded in ADR 0008. |

| PR 2657 | [refactor(fermionic-thermal): derive mixed contractions from BDD](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2657) | Derives both mixed Gibbs contractions and off-diagonal Green-function vanishing through the canonical BDD two-point theorem, removing duplicated occupation-basis coefficient proofs while preserving public APIs. Recorded in ADR 0006. |

| PR 2658 | [refactor(perfect-pairing): internalize crossing pair representation](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2658) | Makes the intermediate crossing-pair subtype and cardinality theorem private while retaining the normalized-pair crossing sum and downstream parity APIs. Recorded in ADR 0008. |

| PR 2659 | [refactor(diagrammatics): narrow component restriction API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2659) | Internalizes same-file crossing and restricted-vacuum normalization specializations, keeping generic normalized-pair crossing and pairing restriction as the reusable APIs. Recorded in ADR 0008. |

| PR 2660 | [refactor(fermionic-thermal): derive anomalous contractions from BDD](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2660) | Derives anomalous free-Gibbs contractions from the canonical BDD two-point API using the zero CAR exchange coefficient, removing a separate charge dependency. Recorded in ADR 0006. |

| PR 2661 | [refactor(diagrammatics): remove trivial component pairing projection](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2661) | Removes a zero-consumer `rfl` projection of the restricted pairing structure field while preserving restriction construction and partner transport. Covered by ADR 0008's public-surface rule; no new decision. |

| PR 2662 | [refactor(fermionic-thermal): inline weighted Green-function branch helpers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2662) | Inlines single-consumer branch helpers but retains the private weighted functional/Gibbs bridge where the off-diagonal theorem still consumes generic time-ordering vanishing; avoids a Gibbs-only wrapper. Recorded in ADR 0006. |

| PR 2663 | [Inline external-insertion component shuffle parity helper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2663) | Inlines a one-use blockwise parity proof into the existing public total-parity theorem, leaving the downstream API unchanged. Covered by ADR 0008's public-surface boundary; no new abstraction. |

| PR 2664 | [refactor(fermionic-thermal): remove weighted Green-function layer](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2664) | Removes the private weighted-coordinate Green-function layer after migrating closed forms and off-diagonal vanishing to density-state expectations and BDD contraction kernels. Recorded in ADR 0006. |

| PR 2665 | [feat(diagrammatics): factor external pairing evaluations](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2665) | Adds a Common factorization of scalar pairing evaluation under component-local pair-kernel values, then identifies the residual inter-component factor with the Fermionic external-component order sign for an explicit order. The result does not provide time-order or physical-amplitude factorization. Recorded in ADR 0008. |

| PR 2666 | [refactor(diagrammatics): internalize quartic component proof glue](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2666) | Makes same-module quartic reassembly/restriction proof and construction helpers private while preserving the semantic restriction, graph-transport, inverse, and connectedness contracts. Recorded in ADR 0008. |

| PR 2667 | [refactor(diagrammatics): narrow quartic component helper API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2667) | Inlines and deletes the one-consumer connectedness proof lemma rather than preserving it as a private name; retains the public connectedness and reassembly endpoints and only keeps useful local proof glue. Recorded in ADR 0008. |

| PR 2668 | [refactor(fermionic-thermal): add BDD-backed timed contraction closed form](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2668) | Closed without merge (`mergedAt: null`). Its proposed BDD-backed closed form would let two-point regularity bypass the generic exponential-factor bridge, while quartic consumers retained that bridge; treat it as an unadopted proposal and make no ADR change. |

| PR 2669 | [refactor(diagrammatics): inline quartic reassembly pairing](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2669) | Inlines a short, one-use private pairing-construction helper into the public semantic `reassemble` constructor. Covered by ADR 0008's helper/API boundary; no separate decision. |

| PR 2670 | [refactor(fermionic-thermal): remove obsolete weighted Gibbs remnants](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2670) | Removes the private weighted-coordinate bridge and unreferenced compatibility/nonzero wrappers after the BDD migration while preserving general powerset factorization and the canonical partition-function API. Recorded in ADR 0006. |

| PR 2671 | [refactor(diagrammatics): remove unused vacuum pairing helper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2671) | Removes a private one-use vacuum partner-transport theorem that restated generic `PairingOn.restrictAlongEquiv_partner`; the shared law remains the canonical reusable boundary. Covered by ADR 0008; no new decision. |

| PR 2672 | [refactor(dyson): inline pair-value bridge proofs](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2672) | Inlines two single-consumer Gibbs bridge proofs into `flatVertexLegPairValue_eq`, preserving the public flattened-leg pair-value API and BDD endpoint. Covered by ADR 0008's endpoint/helper policy; no separate decision. |

| PR 2673 | [refactor(transport): trim conductivity normalization helpers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2673) | Removes unconsumed electric-field-factor simplification lemmas and inlines its sole-use nonzero proof, leaving the conductivity normalization API and theorem statements unchanged. No new ADR decision; physical normalization remains as recorded under ADR 0009/#2535. |

| PR 2674 | [refactor(pairing): share restricted partner transport](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2674) | Moves the shared restricted-pairing partner recovery law into `Combinatorics.PerfectPairing.Restriction`; Quartic and external-insertion layers keep their semantic partner-compatibility endpoints. Recorded in ADR 0002. |

| PR 2675 | [refactor(diagrammatics): narrow external component leg API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2675) | Makes a three-use same-module membership/equality proof helper private while retaining the public semantic component leg maps, order embedding, shuffle, and normalized-pair embedding. Covered by ADR 0008's boundary; no separate decision. |

| PR 2676 | [refactor(dyson): remove unused pairing evaluation simp theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2676) | Removes an unconsumed `@[simp]` expansion theorem while retaining `flatVertexLegPairingEvaluation` as the canonical evaluator and leaving downstream proofs unchanged. Covered by ADR 0008's semantic endpoint/API policy; no separate decision. |

| PR 2677 | [refactor(transport): remove unused common-energy integrability theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2677) | Removes an unconsumed standalone integrability theorem because the actual integral endpoint already proves the needed finite-sum integrability locally; the integral theorem remains unchanged. No new ADR decision. |

| PR 2678 | [refactor: trim unused simp lemmas](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2678) | Deletes genuinely unused private simp lemmas, removes unnecessary global `[simp]` attributes while retaining ordinary theorem statements, and restores indirectly consumed Schwartz simp lemmas after compilation exposed their use. Recorded in ADR 0019. |

| PR 2679 | [refactor(pairing): share component pair product factorization](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2679) | Extracts the normalized-pair product factorization into generic `Combinatorics.PerfectPairing.ComponentDecomposition` for any commutative multiplicative target; Quartic and ExternalInsertion retain distinct residual exchange/crossing factorization. Recorded in ADRs 0002 and 0008. |

| PR 2680 | [refactor: audit private simp attributes](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2680) | Removes global `[simp]` registration from private helper theorems and names required rewrite dependencies explicitly at use sites. Recorded in ADR 0019. |

| PR 2681 | [refactor(massive-dirac): inline radial dominated-convergence helpers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2681) | Calls the generic dominated-convergence theorem directly from the MassiveDirac radial endpoint and discharges model-specific hypotheses locally, removing single-consumer wrappers without changing assumptions or the result. Recorded in ADR 0009. |

| PR 2682 | [refactor(massive-dirac): hide radial DCT proof helpers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2682) | Makes six same-module measurability, domination, and pointwise-limit helpers private while preserving the public finite-radial limit theorem; retains their internal proof decomposition for readability. Recorded in ADR 0009. |

| PR 2683 | [refactor(pairing): share diagonal component crossing theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2683) | Extracts diagonal component-crossing equality to generic `PerfectPairing.ComponentCrossing`, with endpoint compatibility and strict monotonicity hypotheses; diagram-specific embeddings and off-diagonal parity remain downstream. Recorded in ADRs 0002 and 0008. |

| PR 2684 | [refactor(combinatorics): narrow BinaryShuffle import](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2684) | Replaces a whole-Mathlib import with `Mathlib.Data.Fintype.BigOperators` while preserving shuffle theorem interfaces; downstream leaves add their own direct dependencies. Covered by ADR 0010's narrow-import boundary; no new decision. |

| PR 2685 | [refactor(dyson): inline pair-value continuity proof](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2685) | Removes the single-consumer public pair-value continuity theorem and proves continuity directly in the canonical pairing-evaluation endpoint. Covered by ADR 0008's semantic endpoint/helper boundary; no separate decision. |

| PR 2686 | [refactor(dyson): remove unused cardinality amplitude theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2686) | Removes an unused convenience theorem equating total Wick amplitudes by vertex-set cardinality; the canonical Dyson-to-Wick endpoint remains. Covered by ADR 0008's API policy; no separate decision. |

| PR 2687 | [refactor: make private simp dependencies explicit](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2687) | Removes private `[simp]` registrations and names required rewrites explicitly, deletes a zero-consumer length lemma, and preserves genuinely shared Schwartz simplification boundaries. Recorded in ADR 0019. |

| PR 2688 | [refactor(theory): reuse general downstream APIs](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2688) | Removes duplicated MassiveDirac, Fermionic vacuum, and Fermionic completed-space wrappers in favor of the existing generic band-filling and Common APIs. Recorded in ADR 0002. |

| PR 2689 | [refactor: clean audit wrappers and stale retention entries](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2689) | Replaces one-use external-label and Pauli wrappers with existing general theorems and re-audits catalog exceptions: one theorem entry is gone with its declaration, while three entries are no longer required although their declarations remain. Recorded in ADRs 0002 and 0020. |

| PR 2690 | [refactor(validation): use generic Lehmann denominator theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2690) | Moves fixed-rate denominator nonvanishing beside its scalar definition, removes the duplicate unit-hbar dimer theorem, and preserves the limit-layer and physical response contracts. Recorded in ADR 0009. |

| PR 2691 | [refactor(field): remove redundant L2 apply wrapper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2691) | Removes an unconsumed simp theorem that only restated the apply law of its generic `L2MultiplicationRealLine` owner; the canonical fermionic charge-density definition remains. Covered by ADR 0002's specialization boundary; no separate decision. |

| PR 2692 | [refactor(fermionic): use common completed-space facts](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2692) | Removes Fermionic basis-state and dense-range wrappers for the completed-space map; consumers specialize the statistics-independent Common facts directly while retaining Fermionic operators and compatibility endpoints. Recorded in ADR 0002. |

| PR 2693 | [refactor: trim remaining local private simp rules](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2693) | Removes unnecessary private `[simp]` registrations, makes a coefficient rewrite explicit at its consumer, and inlines a one-use helper while preserving public declarations. Recorded in ADR 0019. |

| PR 2694 | [refactor(dyson): remove unused thermal import](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2694) | Removes a direct `FreeBoltzmannCore` import unused by Dyson pairing while leaving declarations and proofs unchanged; the leaf keeps only its actual thermal dependencies. Covered by ADRs 0002 and 0010; no new decision. |

| PR 2695 | [refactor: trim remaining private simp boundaries](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2695) | Reuses the existing Schwartz real/imaginary-part owner and localizes private derivative/conjugation/time-transport rewrite dependencies instead of globally registering them. Recorded in ADRs 0002 and 0019. |

| PR 2696 | [refactor: narrow public simp normalization rules](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2696) | Removes `[simp]` from public whole-equivalence/inverse identities while keeping their theorem statements for explicit `rw`; pointwise evaluation rules remain the canonical simplifier boundary. Recorded in ADR 0019. |

| PR 2697 | [refactor(diagrammatics): inline component crossing wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2697) | Removes Quartic and ExternalInsertion one-use diagonal crossing wrappers and applies generic `Pairing.componentCrossingCount_self_eq` directly at both endpoints. Recorded in ADR 0008. |

| PR 2698 | [refactor(two-point): inline mixed crossing locality helper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2698) | Inlines a single-consumer crossing-preservation proof into its TwoPoint same-order-chamber weight endpoint, avoiding a generic theorem without independent reuse. Recorded in ADR 0008. |

| PR 2699 | [refactor(massive-dirac): narrow denominator proof API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2699) | Localizes arbitrary-regulator derivative, slit-plane, logarithmic-antiderivative, and UV proof steps while retaining physical-side denominator identities and the final UV theorem. Recorded in ADR 0009. |

| PR 2700 | [refactor(combinatorics): specialize partition order decomposition](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2700) | Adds a sized generic family-order decomposition and implements `Finpartition` as an adapter, retaining partition-facing `Finset.card` APIs/nonempty parts and generic empty fibers. Recorded in ADRs 0002 and 0008. |

| PR 2701 | [refactor(massive-dirac): narrow boundary proof API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2701) | Makes the full complex denominator `Tendsto` result the canonical boundary theorem, inlining the real-coordinate proof and the single-use channel-weight limit helper while preserving downstream complex/self-energy endpoints. Recorded in ADR 0009. |

| PR 2702 | [refactor(streda): unify pure-point spectral sides](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2702) | Closed without merge (`mergedAt: null`). It proposed sharing the Retarded/Advanced pure-point resolvent calculations through local `SpectralSide` proofs in one Středa trace theorem; treat as unadopted and make no ADR change. |

| PR 2703 | [feat(ahe): normalize Gaussian crossed conductivity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2703) | Adds the finite-cutoff/broadening ordered-`xy` `X`/`Psi` conductivity with `(ev)^2` and trace-only Bastin normalization, because the upstream Fourier blocks already carry the physical momentum measure and correlators. Proves zero-disorder vanishing and `Psi` reality; leaves evaluation and limits open. Recorded in ADR 0009. |

| PR 2704 | [refactor(bastin): unify radial spectator side bounds](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2704) | Replaces duplicated R/A radial denominator and resolvent bounds with one public `SpectralSide`-indexed inverse-margin theorem and a private side-indexed helper, preserving the uniform hypotheses and result. Recorded in ADR 0009. |

| PR 2705 | [refactor(combinatorics): remove coordinate-change wrapper](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2705) | Deletes the project-local equivalence coordinate-change module and uses standard `source.symm.trans target` composition at all consumers; no coordinate semantics change. Updates ADR 0002, superseding the wrapper choice from #2569 while retaining the removal of shuffle-specific permutation machinery. |

| PR 2706 | [feat(analysis): prove radial Fourier kernel parity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2706) | Establishes generic full-angle Fourier-kernel parity through a half-period angular shift (`K0`,`K2` even; `K1` odd), enabling negative-radius crossed-block simplification without Bessel identification or value/limit claims. Recorded in ADR 0009. |

| PR 2707 | [feat(ahe): prove crossed real-space block parity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2707) | Proves side-indexed Green radial reflection by `σz` conjugation and crossed-current reflection by negative `σz` conjugation at their physical block owners, enabling downstream scalar reduction without claiming values or limits. Recorded in ADR 0009. |

| PR 2708 | [refactor(transport): trim angular harmonic wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2708) | Keeps `AngularHarmonicCoefficients.integral_eval` as the public full-angle boundary, makes primitive facts private, and removes a single-use constant/first-harmonic wrapper. Recorded in ADR 0009. |

| PR 2709 | [refactor(operator): consolidate narrow operator modules](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2709) | Folds vectorwise evolution, resolvent generator, diagonal positivity, and `L²` multiplication facts into canonical owners; keeps a one-consumer eigenbasis helper private and removes five proof-stage/single-specialization modules without forwarding aliases. Recorded in ADR 0002. |

| PR 2710 | [feat(disorder): prove finite SCBA charge Ward bridge](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2710) | Adds two-sided exact second-moment equivariance, minimal bounded `ChargeSymmetry`, and the finite SCBA/generic-RA charge-vertex identity under `IsUnit (1 - L_RA)`, without claiming conductivity, full Ward–Takahashi, or limits. Recorded in ADR 0009. |

| PR 2711 | [feat(ahe): eliminate negative-radius crossed trace blocks](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2711) | Rewrites Gaussian-crossed `X/Psi` entry sums and scalar momentum-integral boundaries to positive radius with explicit diagonal `σz` factors/current sign, preserving topology and making no value/limit claim. Recorded in ADR 0009. |

| PR 2712 | [refactor(analysis): share scalar exchange peel](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2712) | Generalizes the finite scalar-exchange peel to associative unital complex algebras and shares it between Bose/Fermi BDD at `ζ = ±1`; replaces the narrower `Analysis.Operator.ExchangePeel` owner and removes the duplicate fermionic recursion. Recorded in ADRs 0002 and 0006. |

| PR 2713 | [feat(ahe): scalarize crossed radial traces](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2713) | Adds shared scalar/vector Pauli coordinates and compact two-/four-factor trace identities, then expresses the finite-cutoff crossed `X/Psi` kernels as positive-radius scalar dot/cross formulas. Radial integration, limits, and benchmark values remain open. Recorded in ADRs 0002 and 0009. |

| PR 2714 | [refactor(analysis): generalize zeta commutator ownership](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2714) | Moves fixed-sign bracket laws into generic `Analysis.ScalarExchange`, migrates Common/Bose/Fermi consumers, and preserves semantic endomorphism APIs through explicit specialization bridges. Recorded in ADRs 0001 and 0002. |

| PR 2715 | [feat(imaginary-time): generalize external insertion mixed order](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2715) | Adds minimal higher-point mixed ordering for `2 * E` external insertions and `n` interaction events, expands event order to atomic legs, and keeps it separate from the mature two-point representation. Deferred helpers await an amplitude consumer. Recorded in ADR 0008. |

| PR 2716 | [feat(ahe): expose crossed radial Pauli coefficients](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2716) | Exposes model-owned scalar/vector coefficients for radial Green/current blocks as combinations of existing entry-kernel integrals and removes raw matrices from crossed scalar trace endpoints. Explicit `K0/K1/K2` integration, limits, and final values remain open. Recorded in ADR 0009. |

| PR 2717 | [refactor(calculus): remove unused symmetric-localization wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2717) | Deletes duplicate represented/intrinsic symmetric-localization packaging with no consumers; one-particle owners construct balance laws directly from reusable localization algebra and canonical APIs. Recorded in ADR 0002. |

| PR 2718 | [feat(external-insertion): add timed-field pairing semantics](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2718) | Adds a Fermionic consumer over canonical insertion legs, reusing Common mixed order for timed-field pair contractions and transported pairing evaluation; defers time-order sign and scalar interaction weight to the amplitude. Recorded in ADR 0008. |

| PR 2719 | [feat(ahe): expose crossed radial Pauli kernels](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2719) | Proves pointwise scalar/vector coefficient kernels in the existing zeroth/first/second angular Fourier channels without changing integrated coefficient APIs or assuming integral linearity without integrability. No Bessel identification or limits. Recorded in ADR 0009. |

| PR 2720 | [refactor(quantum): move orbital angular momentum ownership](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2720) | Moves physical one-particle orbital-angular-momentum identities out of `Analysis.Operator` into `QuantumMechanics.SingleParticle`, retaining generic commutator algebra upstream and removing the old path without aliases. Recorded in ADR 0002. |

| 2721 | [refactor: bundle the fixed-cutoff metallic Born regime](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2721) | Implemented by [PR #2722](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2722): introduces a shared MassiveDirac fixed-cutoff metallic Born domain package for selected zero-broadening boundaries, while keeping normalization and result-specific hypotheses explicit. Recorded in ADR 0009. |

| PR 2722 | [refactor(massive-dirac): bundle fixed-cutoff Born regime](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2722) | Merged implementation of issue #2721. Its diff was reviewed as part of that issue; it adds no separate architectural decision beyond the ADR 0009 record above. |

| 2723 | [refactor: deduplicate fixed-cutoff regime adapter construction](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2723) | Implemented by [PR #2725](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2725): scalar adapters use the named `ofScalarBoundaryData` constructor; regime-native proofs pass the original package without reconstruction. No physical assumptions or API meanings change. Recorded in ADR 0009. |

| PR 2724 | [refactor(kubo-bastin): reuse generic common-energy kernel](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2724) | Specializes the generic measured/source common-energy Kubo–Bastin kernel for Fermionic directional current, reuses its generic integral API, removes duplicated transition wrappers, and keeps interval localization generic. Recorded in ADR 0009. |

| PR 2725 | [refactor(massive-dirac): deduplicate regime adapters](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2725) | Merged implementation of issue #2723. Its diff was reviewed as part of that issue; no separate domain decision beyond the ADR 0009 adapter-boundary record. |

| PR 2726 | [feat(ahe): bridge radial Pauli coefficients to kernels](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2726) | Closed without merge and has no diff. Its broad bridge was not adopted in that PR; narrower Green-only and crossed-current bridges later landed in #2731 and #2741, and #2742 derives finite-broadening finite-cutoff integrability from the model assumptions. Cutoff removal and limits remain open. |

| PR 2727 | [refactor(kubo-bastin): inline single-use common-energy proof](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2727) | Inlines the last private one-use bridge into its sole conductivity theorem consumer after #2724's generic-kernel migration; public endpoints and interval localization remain unchanged. Recorded in ADR 0009. |

| PR 2728 | [feat(external-insertion): add fixed-time amplitude](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2728) | Combines the fixed-to-mixed fermionic permutation sign, generic diagram vertex weight, and mixed-time pairing value into a fixed-time amplitude; no separate interaction-order sign or component factorization is added. Recorded in ADR 0008. |

| PR 2729 | [feat(external-insertion): add component-local amplitude data](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2729) | Reindexes each restricted component to consecutive interaction slots, preserving canonical external order and pairing while exposing induced component times. Pair-kernel locality and product factorization remain open. Recorded in ADR 0008. |

| PR 2730 | [refactor(analysis): clean up flat analysis modules](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2730) | Leaves flat Analysis roots as routers, splits scalar-exchange implementation into algebra/peel leaves, removes an unused normalized-functional abstraction, inlines a one-use ladder helper, and narrows consumer imports. Recorded in ADRs 0002 and 0006. |

| PR 2731 | [feat(ahe): bridge radial Green Pauli coefficients](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2731) | Adds a Green-only bridge from integrated Pauli coefficients to pointwise kernels under explicit entrywise interval-integrability; #2742 later derives those hypotheses from finite-broadening finite-cutoff assumptions. The crossed-current analogue lands in #2741. Recorded in ADR 0009. |

| PR 2732 | [feat(external-insertion): add component field locality](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2732) | Embeds each component-local canonical leg into the ambient order and proves its field label and `TimedField` are inherited; no mixed-position or pair-contraction transport is added. Recorded in ADR 0008. |

| PR 2733 | [refactor(analysis): remove single-leaf forwarding routes](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2733) | Deletes `Analysis.InternalSpace` and `Analysis.FunctionalCalculus` forwarding files because each had one leaf and no consumers; `Analysis.lean` imports those leaves directly. Recorded in ADR 0002. |

| PR 2734 | [refactor(analysis): expose Stone evolution by semantic name](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2734) | Renames the consumer-facing limiting group and its public laws to `stoneEvolution`; leaves `resolventApproximation...` on the approximation method and bounds. Mathematical results are unchanged. Recorded in ADR 0002. |

| PR 2735 | [feat(disorder): expose universal identity charge symmetry](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2735) | Confirms the already-recorded ADR 0009 boundary: identity is a `ChargeSymmetry` for every finite disorder ensemble, independent of scalar covariance, and a compiled anonymous example exercises the generic SCBA/RA Ward theorem. No MassiveDirac wrapper is added. |

| 2736 | [refactor(massive-dirac): move zero-broadening tensor seam out of Hall](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2736) | Implemented by [PR #2739](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2739): moves tensor-level zero-broadening, convergence, and rotational identities to a neutral Conductivity owner; Hall consumes the completed tensor projection. Recorded in ADR 0009. |

| PR 2737 | [refactor(analysis): move model-specific Pauli traces downstream](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2737) | Moves one-consumer MassiveDirac projector/coordinate trace formulas out of generic Pauli Analysis and keeps them local to their model consumers. Generic Pauli algebra remains shared. Recorded in ADR 0002. |

| PR 2738 | [refactor(audit): resolve single-consumer findings](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2738) | Removes two proof-routing wrappers in favor of canonical slot-order and angular-harmonic APIs; explicitly retains eight low-consumer declarations with independent mathematical or physical meaning. Records the consumer-count audit rule in ADR 0002 and applies it in ADRs 0008 and 0009. |

| PR 2739 | [refactor(massive-dirac): move tensor zero-boundary seam out of Hall](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2739) | Merged implementation of issue #2736, already reviewed with that issue and recorded in ADR 0009; this PR adds no separate architectural disposition. |

| 2740 | [refactor(ordered-simplex): remove dead measurable integral-bound module](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2740) | Deletes an unused proof-stage module and stale import; the consumer retains its distinct boundary-integrability theorem from the semantic owner. Recorded in ADR 0002. |

| 2741 | [feat(ahe): bridge radial current Pauli coefficients](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2741) | Adds conditional finite-integral bridges for the Gaussian-crossed radial current's scalar and all Pauli coefficients under explicit entrywise interval-integrability, matching the #2719 pointwise kernels. The assumption burden is discharged for the finite-broadening finite-cutoff regime by #2742. Recorded in ADR 0009. |

| 2742 | [feat(ahe): discharge radial kernel integrability](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2742) | Proves continuity and interval-integrability of generic radial Fourier kernels and all model Green/current entry kernels under finite broadening, nonnegative disorder, and nonnegative cutoff; integrated coefficient APIs now take those direct conditions. Does not remove cutoffs or take limits. Recorded in ADR 0009. |

| 2743 | [refactor(audit): resolve cross-module single consumers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2743) | Removes a one-use operator wrapper and routes through its canonical field-level theorem; explicitly retains 64 low-consumer declarations with independent mathematical, analytic, combinatorial, or physical meaning. Recorded in ADRs 0002 and 0008. |

| 2744 | [refactor(ordered-simplex): collapse family shuffle proof stages](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2744) | Makes the arbitrary-finite-type measurable family-shuffle identity the canonical API, labels continuity as a specialization, and keeps `Fin k` recursion/transport internal; removes redundant forwarding modules and migrates the quartic Wick consumer. Recorded in ADRs 0002 and 0008. |

| 2745 | [refactor(analysis): separate conservation laws from calculus](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2745) | Moves semantic current and balance-law modules under `Analysis.ConservationLaw`, narrows the Calculus umbrella, and updates source contracts/topology while preserving dependency direction. Recorded in ADR 0002. |

| 2746 | [refactor(ordered-simplex): privatize binary shuffle proof stages](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2746) | Makes two one-consumer recursive contribution equalities private while preserving the public product identities and ambient slot-shuffle API. Recorded in ADR 0002. |

| 2747 | [refactor(analysis): move localization algebra into conservation laws](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2747) | Completes the conservation package move by transferring shared localization operator algebra and corrected-current flux out of Calculus, updating routes/contracts without changing dependency intent. Recorded in ADR 0002. |

| 2748 | [refactor(ordered-simplex): remove continuous family-shuffle wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2748) | Removes zero- and one-consumer continuous-only specializations of the generic family-shuffle product theorem; the consumer supplies continuity-to-measurable-local-boundedness directly. Recorded in ADRs 0002 and 0008. |

| 2749 | [refactor: simplify combinatorics with Mathlib APIs](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2749) | Uses `Equiv.Set.sumDiffSubset`, `Finset.card_filter`, and `Finset.sum_product` for generic construction/counting while retaining project-facing domain API names. Recorded in ADR 0002. |

| 2750 | [docs(conventions): define simp lemma policy](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2750) | Defines global `[simp]` as a canonical-normal-form/API-boundary choice; keeps ambiguous or substantive rewrites explicit and distinguishes `simp`, `simp only`, and `rw`. Updated ADR 0019. The PR is documentation-only. |

| 2751 | [refactor(two-point): remove direct theorem wrappers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2751) | Removes two `rfl` specialization wrappers and migrates private consumers to the canonical cardinality-transport theorems. Recorded in ADRs 0002 and 0008. |

| 2752 | [refactor(simp): audit canonical simplification boundaries](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2752) | Adds a reviewed global simp registry, removes eight noncanonical global simp tags while retaining the theorems for explicit use, and marks unlisted entries as pending review. Recorded in ADR 0019. |

| 2753 | [refactor: reuse sigma product helper for finpartitions](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2753) | Reuses `Fintype.prod_equiv_sigma` for the finpartition product decomposition, preserving the public theorem while removing duplicate reindexing proof code. Recorded in ADR 0002. |

| 2754 | [docs(catalog): retain canonical family shuffle product theorem](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2754) | Removes the retained entry for the retired continuous wrapper and records the canonical general measurable product theorem despite its single private consumer. Recorded in ADRs 0002 and 0008. |

| 2755 | [refactor: reuse Finset.equivMap for sum-image subtypes](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2755) | Closed without merge. The proposal would build project-facing image-subtype equivalences with Mathlib's `Finset.equivMap`, but it is not adopted evidence for the repository's current implementation or ownership decision. No ADR change. |

| 2756 | [refactor: hide scalar-exchange implementation bridges](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2756) | Removes the unconsumed public `ζ = ±1` equations from semantic `linearCommutator`/`symmetrizedProduct` APIs and drops an unnecessary generic-algebra import. Recorded in ADRs 0001 and 0002. |

| 2757 | [refactor(dyson): privatize raw exponential derivative](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2757) | Makes a one-consumer raw derivative identity private while preserving the simplified public derivative theorem. Recorded in ADR 0002. |

| 2758 | [refactor: use Mathlib to bundle the Stone strong limit](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2758) | Uses Mathlib's bounded pointwise-limit construction for the Stone evolution, deleting project-owned additivity, scalar-linearity, and intermediate linear-map stages while preserving the public endpoint. Recorded in ADRs 0001 and 0002. |

| 2759 | [refactor(simp): resolve remaining yellow boundaries](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2759) | Completes the reviewed simp audit: canonical rules are registered Green, four analytic/physical identifications remain explicit-only, and Hall-to-ordered-`xy` rewrites are explicit while direct `sxx` projections remain simp. Recorded in ADRs 0009 and 0010. |

| 2760 | [refactor(transport): decouple AHE scaling coordinates from transport domains](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2760) | Completed by [PR #2763](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2763), which separates minimal Born-RTA physical inputs, finite-cutoff pair data, and scaling-only energy coordinates without changing formulas or limit order. The same PR also closes #2761; its self-energy API cleanup is recorded when that issue is reviewed. Recorded in ADR 0009. |

| 2761 | [refactor(impurity): narrow the MassiveDirac Born self-energy public surface](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2761) | Implemented with #2760 by [PR #2763](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2763): retains downstream-used self-energy and denominator APIs while making zero-caller polar/proof decompositions private, with formulas and limits unchanged. Recorded in ADR 0009. |

| 2762 | [refactor(linear-response): reduce internal API surface](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2762) | Makes a one-use Kubo commutator functional and Dyson first-term theorem private, localizes an adjoint-isometry proof helper, and removes an unused integrability alias while preserving public response formulas. Recorded in ADR 0009. |

| PR 2763 | [refactor(transport): separate AHE scaling coordinates and narrow Born self-energy API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2763) | Merged implementation of issues #2760 and #2761, reviewed with those issues and recorded in ADR 0009; no additional decision beyond their combined dispositions. |

| 2764 | [refactor(linear-response): centralize free dynamics structure](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2764) | Moves generic propagator and Heisenberg-evolution structure to `FreeDynamics`, bundling the propagator as a unitary and reusing Mathlib's star-algebra automorphism for algebra laws. Recorded in ADRs 0001 and 0009. |

| 2765 | [refactor(linear-response): narrow Lehmann limit API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2765) | Privatizes finite-family response sums and their supporting limit lemmas while preserving the public pure-point theorem and explicit limit-order/nonresonance contract. Recorded in ADR 0009. |

| 2766 | [refactor: make Stone Cauchy extension filter-native](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2766) | Exposes domain convergence as `CauchySeq` and factors dense-set extension for isometry families into a reusable metric-space theorem, preserving the quantitative estimate. Recorded in ADR 0002. |

| 2767 | [fix(ci): reduce theorem catalog false positives](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2767) | Keeps generated extension declarations in the full catalog but excludes them from unresolved queues, recognizes unambiguous short retained names, and reruns the advisory catalog job when disposition documents change. Recorded in ADR 0020. |

| 2768 | [refactor(spin-hall): route spin response through ResponseChannel](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2768) | Adds the finite spin-z current/electric bond-source channel and routes the old retarded susceptibility through its kernel without changing observable/source roles or expanding spin-Hall claims. Recorded in ADR 0009. |

| 2769 | [refactor(linear-response): narrow physical limit API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2769) | Makes a totalized susceptibility extension and local/intermediate limit-order packages private while preserving the public finite-time physical three-stage response theorem. Recorded in ADR 0009. |

| 2770 | [refactor(linear-response): centralize local limit-order predicates](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2770) | Moves generic local two- and three-stage limit predicates to `LinearResponse.LimitOrder`; Lehmann modules retain concrete existence results and physical applications. Recorded in ADR 0009. |

| 2771 | [refactor: use Mathlib dense Lipschitz continuity extension](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2771) | Reuses Mathlib's dense Lipschitz product-continuity theorem to extend continuity from the generator domain via isometric time slices; keeps the quantitative domain estimate separate. Recorded in ADRs 0001 and 0002. |

| 2772 | [refactor(linear-response): remove unused global limit predicates](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2772) | Deletes unconsumed global two-/three-stage order predicates and trivial constructors, preserving local limit-order APIs needed by finite Lehmann results where resonances can exist away from zero. Recorded in ADR 0009. |

| 2773 | [refactor(linear-response): inline trivial Lehmann limit helpers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2773) | Inlines three one-use finite-sum lifting lemmas, retains the nontrivial regulator-removal induction privately, and preserves the canonical zero-rate transition term. Recorded in ADR 0009. |

| 2774 | [refactor(spin-hall): generalize spin-current polarization](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2774) | Closed without merge. The proposal replaces spin-z with arbitrary real Pauli polarization and adds a commutation-based intrinsic-current condition; it is not adopted as the current response API. No ADR change. |

| 2775 | [refactor: trim Stone continuity implementation API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2775) | Makes the dense-domain continuity theorem private and removes unused pointwise continuity wrappers/time-shift helper, retaining joint and orbit continuity endpoints. Recorded in ADR 0002. |

| 2776 | [refactor: inline Stone unitarity proof helpers](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2776) | Removes one-use negative-time inverse theorems and inlines inner-product preservation in the adjoint proof, preserving public group/adjoint/unitary laws and consumed strong-limit facts. Recorded in ADR 0002. |

| 2777 | [refactor(thermal): reuse pure-point entropy identity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2777) | Uses the generic pure-point Gibbs entropy theorem in the free-fermion specialization, removing five proof-routing results while retaining physical marginal, mean-energy, and binary-entropy endpoints. Recorded in ADR 0016. |

| 2778 | [refactor: hide Stone domain resolvent machinery](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2778) | Makes resolvent-approximation commutation stages and the vectorwise limit proof private, removes an unused operator wrapper, and retains semantic domain-preservation APIs. Recorded in ADR 0002. |

| 2779 | [refactor(current): unify generalized current API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2779) | Makes `Analysis.ConservationLaw` the single owner of symmetrized/corrected flux algebra, removes the `ConventionalCurrent` compatibility layer and duplicate wrappers, and routes generic bounded Fock current and spin-z response through the symmetrized-velocity API. Recorded in ADRs 0002 and 0009. |

| 2780 | [refactor(lattice): audit discrete continuity API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2780) | Removes unused matrix-unit specializations and inlines one-consumer proof routes while retaining canonical locality, orientation, commutator, and discrete continuity APIs; the algebraic continuity theorem remains the source endpoint for bounded finite-lattice continuity. Recorded in ADR 0002. |

| 2781 | [refactor: share the resolvent approximation scale](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2781) | Exposes the totalized operator approximation, strong convergence, and shared scale at the resolvent-evolution Cauchy boundary; the generator consumes that owner instead of keeping a duplicate scale API, while substantial derivative proof stages remain local. Recorded in ADR 0002. |

| 2782 | [refactor(validation): audit finite transport toys](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2782) | Moves simultaneous-current-sign symmetry to the generic Středa operator-kernel API, removes one-consumer proof wrappers and toy-specific simp rules, and retains the concrete zero-current endpoint plus reusable toy data. Recorded in ADR 0009. |

| 2783 | [refactor(current): expose current as a proposition](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2783) | Names current-ness as a relation among the differential, intrinsic transport, and selected one-form current; exposes representation proof fields, preserves representation-independent differential dependence, and adds no compatibility alias for the old factorization name. Recorded in ADR 0002. |

| 2784 | [refactor: keep Stone generator proof on public evolution API](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2784) | Makes arbitrary-time generator transport use `stoneEvolution_add` and `stoneEvolution_zero` instead of lower-level strong-limit implementation lemmas, while retaining the substantive private intertwining stage and quantitative slope estimate. Recorded in ADR 0002. |

| 2785 | [refactor(validation): finish finite toys audit](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2785) | Inlines the one-use two-level Hilbert basis and zero-current operator into the retained Středa endpoint, and removes a duplicate omission directive from the generic current-sign theorem. Recorded in ADR 0009. |

| 2786 | [refactor(current): move differential dependence upstream](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2786) | Moves `DependsOnlyOnDifferential` and its closure/kernel characterizations to `CurrentRepresentation`, upstream of balance-law objects; characterizes it by kernel inclusion and renames the implication from a chosen current. Recorded in ADR 0002. |

| 2787 | [refactor: transport Stone derivative by composition](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2787) | Derives arbitrary-time Stone evolution differentiability by composing the zero-time derivative with the fixed evolution and translating time, removing a manual slope-limit argument while preserving quantitative generator estimates. Recorded in ADR 0002. |

| 2788 | [refactor(current): center equivalence on current predicate](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2788) | Moves same-transport current equivalence onto `IsDifferentialCurrent`, adds invariance under exact-differential equivalence, and keeps the representation structure as a current-plus-proof bundle. Recorded in ADR 0002. |

| 2789 | [refactor(spin): derive polarization from physical direction](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2789) | Introduces a real three-dimensional spin-component space and a spin-1/2 representation map; spin-current APIs now accept arbitrary polarization vectors, while generic two-level operator algebra stays analysis-only and Pauli axes remain representation coordinates. Recorded in ADRs 0002 and 0009. |

| 2790 | [docs: clarify umbrella module descriptions](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2790) | Rewrites umbrella descriptions in terms of their collected mathematical or physical APIs, retaining dependency-boundary rationale only where it constrains current architecture; documentation-only. Recorded in ADR 0002. |

| 2791 | [docs: describe current semantic responsibilities](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2791) | Rewrites non-umbrella module documentation around present mathematical/physical responsibility, refreshes the generic/specialized fermionic transport description, and states the simp registry as standing policy rather than dated audit history; documentation-only. Recorded in ADRs 0002 and 0019. |

| 2792 | [refactor: use zero-time simp API in Stone generator](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2792) | Reuses the existing zero-time simp laws in the generator derivative proof, removing local evaluation rewrites while preserving the quantitative estimate and public API. Recorded in ADR 0002. |

| 2793 | [docs: clarify subtree module semantics](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2793) | Rewrites nested module docs around present mathematical/physical responsibility, removes development-sequence and roadmap wording, and preserves genuine technical descriptions; documentation-only. Recorded in ADR 0002. |

| 2794 | [refactor: simplify Stone slope estimate algebra](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2794) | Replaces a private common-basepoint algebra proof and `field_simp` cancellation with Mathlib's `sub_sub_sub_cancel_right` and `inv_mul_cancel₀`; the quantitative estimate is unchanged. Recorded in ADR 0001. |

| 2795 | [refactor(spin): expose spin-current linearity](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2795) | Makes the symmetrized product explicitly bilinear, derives fixed-slot linear maps, and composes them to expose real-linearity from spin-space input to the measured current density; reviews the corresponding simp boundaries. Recorded in ADRs 0002, 0009, and 0019. |

| 2796 | [feat(external-insertion): add pair-kernel locality](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2796) | Embeds component-local mixed-time positions through canonical ambient legs and exposes free-Gibbs pair-kernel locality; keeps field-family transport private and adds no broader mixed-order framework or component-amplitude factorization. Recorded in ADR 0008. |

| 2797 | [refactor(conservation): isolate differential dependence](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2797) | Moves the representation-independent differential-dependence predicate and its algebra into a dedicated leaf upstream of both current representations and intrinsic balance laws; public theorem names stay unchanged and source contracts/topology record the seam. Recorded in ADR 0002. |

| 2798 | [refactor: inline Stone domain nonreal witnesses](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2798) | Inlines three one-use nonreal-parameter witnesses while preserving semantic resolvent-commutation and domain-invariance proof stages. Recorded in ADR 0002. |

| 2799 | [feat(external-insertion): expose mixed leg positions](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2799) | Exposes the canonical leg-to-mixed-position inverse map and its computation laws, reuses it in component embedding, and defers mixed-order restriction/`StrictMono` until a concrete consumer can use generic combinatorics. Recorded in ADR 0008. |

| 2800 | [feat(external-insertion): add canonical leg reindexing](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2800) | Adds a statistics-independent canonical-leg reindexing map with injectivity from its external/interaction slot maps; component embedding delegates to it without asserting event-order preservation. Recorded in ADR 0008. |

| 2801 | [refactor: derive Stone continuity from local Lipschitz bound](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2801) | Uses Mathlib's local-Lipschitz continuity theorem with the existing generator-domain displacement estimate instead of a manual epsilon-delta proof; estimate and public endpoints are unchanged. Recorded in ADRs 0001 and 0002. |

| 2802 | [refactor: transport Stone continuity by composition](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2802) | Transports continuity from zero to arbitrary time by composing with a time shift and fixed Stone evolution, then applying the group law; removes manual epsilon-delta translation. Recorded in ADR 0002. |

| 2803 | [refactor(transport): make directional responses channel-first](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2803) | Packages finite directional measured/source/contact-variation operators as a `ResponseChannel`, migrates spectral/occupation/common-energy consumers to channel-level APIs, and keeps transition terms generic while hiding explicit-vertex response wrappers. Recorded in ADR 0009. |

| 2804 | [feat(external-insertion): preserve mixed event order](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2804) | Proves that increasing external/interaction slot maps preserve stable mixed-time event order as a sublist of the ambient ordered event list; stops at events and defers atomic-leg strict monotonicity. Recorded in ADR 0008. |

| 2805 | [refactor(ordered-simplex): fold binary shuffle integrand](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2805) | Folds a one-consumer proof-stage module into its canonical binary-shuffle consumer, retaining the ambient integrand while privatizing recursive bridges and inlining unused/single-use helpers. Recorded in ADR 0002. |

| 2806 | [refactor(unbounded): fold bounded evolution estimates](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2806) | Moves reusable norm-preservation and displacement estimates into `BoundedUnitaryEvolution`, inlines a one-use derivative-norm helper, and removes a separate estimate module. Recorded in ADR 0002. |

| 2807 | [refactor(ordered-simplex): fold measurable calculus](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2807) | Folds one-consumer measurable/absolute-continuity calculus support into the public product-split consumer, keeps support theorems private, and retains the long FTC proof as a local helper. Recorded in ADR 0002. |

| 2808 | [refactor(fredholm): consolidate diagonal determinant modules](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2808) | Moves finite-dimensional determinant compatibility into the diagonal Fredholm owner, retains the public compatibility theorem, and deletes the single-child forwarding module. Recorded in ADRs 0002 and 0014. |

Pull requests #2809–#2825 are skipped in this issue-focused pass.

| 2826 | [refactor(transport): deepen the MassiveDirac current-rung response seam](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2826) | Extended ADR 0009: expose source-indexed dressed current and reduced longitudinal outputs through a Disorder-owned seam; keep total algebraic values distinct from the regularity condition for physical fixed-point interpretation, and preserve Středa, crossed-kernel, normalization, and zero-broadening ownership. Implemented by PR #2827. |

Pull requests #2828–#2833 are skipped in this issue-focused pass.

| 2834 | [feat(transport): formalize a finite Rashba-exchange anomalous Hall model](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2834) | Extended ADRs 0009 and 0018: preserve separation from Rashba spin-Hall and MassiveDirac; make finite-model parameters and the Hamiltonian/current/Berry/normalization boundaries explicit, while treating disorder response and all limit claims as future work. The issue remains open. |

| 2835 | [feat(transport): formalize a finite parabolic 2DEG transport benchmark](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2835) | Extended ADR 0009: add an independent explicit-parameter finite 2DEG model, use the common finite-broadening Středa response seam, keep raw response separate from conductivity normalization, and bound Drude/Kubo identities to stated hypotheses. Implemented by PR #2864. |

| 2836 | [feat(topology): formalize a finite QWZ/BHZ Chern-insulator transport benchmark](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2836) | Extended ADRs 0009 and 0018: keep periodic Brillouin-zone/Chern/TKNN integration in a finite model consumer of generic pointwise Berry geometry, make normalization and gap/smoothness assumptions explicit, and distinguish BHZ charge-Hall cancellation from block/spin response. The issue remains open. |

| 2837 | [feat(transport): formalize a finite Weyl-semimetal response model](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2837) | Extended ADRs 0009 and 0018: keep the single-node model a finite 3D continuum benchmark with explicit `k_z` measure/cutoff and punctured-domain Berry data; do not imply lattice regularization, anomaly, Fermi arcs, or unproved limits. The issue remains open. |

| 2838 | [feat(crystal): formalize a finite Kronig–Penney Bloch-band benchmark](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2838) | Extended ADR 0017: reuse the existing Crystal Brillouin momentum/phase convention, while keeping transfer-matrix, discriminant, band/gap, and band-edge data in the finite model; no broader periodic-potential or transport theory is implied. The issue remains open. |

Pull requests #2839–#2864 are not reviewed independently in this issue-focused pass; the linked implementation #2864 is recorded under issue #2835.

No later issue appears in the repository issue list. Resume at the next issue created after #2838.
