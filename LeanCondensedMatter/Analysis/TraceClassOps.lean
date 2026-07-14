import LeanCondensedMatter.Analysis.TraceClassBasic

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# Trace-class compact self-adjoint operators: additive linearity, cyclicity, and trace bounds

Extends `TraceClassBasic.lean`'s `IsTraceClass`/`trace` with the operations needed by downstream
files: `trace_add` (additive linearity), `trace_comp_comm` (cyclicity), and
`sum_inner_apply_le_trace` (a trace upper bound against an incomplete orthonormal family, used by
the Gibbs–Klein / Helmholtz free-energy argument in `QuantumTheory`). All three are proved by
comparing operators against a *common* Hilbert basis of `H`
(`hasSum_inner_apply_eq_trace`), rather than relating individually unrelated eigenbases. See
`notes/roadmaps/operator-algebra.md` (Track C).
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A complex inner product times its "reverse" is the real cast of its squared norm.**
`⟪x,y⟫⟪y,x⟫ = ‖⟪x,y⟫‖²`, a consequence of `⟪y,x⟫` being the complex conjugate of `⟪x,y⟫`
(`inner_conj_symm`) and `z * conj z = normSq z` (`Complex.mul_conj`). Recurs throughout this file
whenever a `HasSum`/Parseval argument needs to turn a product of inner products into a real,
nonnegative quantity. -/
theorem inner_mul_inner_conj_eq_norm_sq (x y : H) :
    (inner ℂ x y * inner ℂ y x : ℂ) = ((‖(inner ℂ x y : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [show (inner ℂ y x : ℂ) = starRingEnd ℂ (inner ℂ x y) from (inner_conj_symm y x).symm,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- **The trace of a finite-rank orthogonal projection, computed against any Hilbert basis of the
ambient space, equals its rank.** The key basis-independence fact underlying `trace`'s additive
linearity: for `V := eigenspace T μ` and summing over all nonzero `μ`, this shows `trace T` can be
computed via *any* orthonormal basis of `H`, not just the eigenbasis used in its definition. -/
theorem tsum_norm_sq_orthogonalProjectionOnto_eq_finrank {ι : Type*} (b : HilbertBasis ι ℂ H)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    ∑' i, ‖V.orthogonalProjectionOnto (b i)‖ ^ 2 = (Module.finrank ℂ V : ℝ) := by
  classical
  set f : Fin (Module.finrank ℂ V) → V := ⇑(stdOrthonormalBasis ℂ V) with hf_def
  -- Step 1: expand each summand via the (finite) orthonormal basis `f` of `V` itself.
  have hpoint : ∀ i, ‖V.orthogonalProjectionOnto (b i)‖ ^ 2 =
      ∑ j, ‖(inner ℂ ((f j : H)) (b i) : ℂ)‖ ^ 2 := by
    intro i
    rw [← (stdOrthonormalBasis ℂ V).sum_sq_norm_inner_right (V.orthogonalProjectionOnto (b i))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  simp_rw [hpoint]
  -- Step 2: each individual term, summed over `i`, is summable (Parseval for `b`).
  have hterm : ∀ x : H, (fun i => ‖(inner ℂ x (b i) : ℂ)‖ ^ 2) =
      (fun i => (inner ℂ x (b i) * inner ℂ (b i) x : ℂ).re) := by
    intro x
    funext i
    rw [inner_mul_inner_conj_eq_norm_sq, Complex.ofReal_re]
  have hj : ∀ j, Summable (fun i => ‖(inner ℂ ((f j : H)) (b i) : ℂ)‖ ^ 2) := fun j => by
    rw [hterm (f j : H)]
    exact ((b.hasSum_inner_mul_inner (f j : H) (f j : H)).mapL Complex.reCLM).summable
  -- Step 3: swap the (finite) `Finset.sum` over `j` with the `tsum` over `i`.
  rw [Summable.tsum_finsetSum (fun j _ => hj j)]
  -- Step 4: each swapped inner tsum is, again by Parseval for `b`, the norm² of `f j` in `H`.
  have hbasis : ∀ j : Fin (Module.finrank ℂ V),
      ∑' i, ‖(inner ℂ ((f j : H)) (b i) : ℂ)‖ ^ 2 = ‖(f j : H)‖ ^ 2 := by
    intro j
    rw [hterm (f j : H)]
    have hs : HasSum (fun i => (inner ℂ ((f j : H)) (b i) * inner ℂ (b i) ((f j : H)) : ℂ).re)
        (inner ℂ ((f j : H)) ((f j : H)) : ℂ).re :=
      (b.hasSum_inner_mul_inner (f j : H) (f j : H)).mapL Complex.reCLM
    rw [hs.tsum_eq, inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hbasis]
  have hnorm1 : ∀ j : Fin (Module.finrank ℂ V), ‖(f j : H)‖ = 1 :=
    fun j => (stdOrthonormalBasis ℂ V).orthonormal.1 j
  simp [hnorm1]

omit [CompleteSpace H] in
/-- **Parseval's identity for a Hilbert basis, in norm-squared form.** For any `x : H`, the
squared-magnitude Fourier coefficients of `x` against a Hilbert basis `d` sum (unconditionally)
to `‖x‖ ^ 2`. -/
theorem _root_.HilbertBasis.hasSum_norm_sq_inner {ι : Type*} (d : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖(inner ℂ x (d i) : ℂ)‖ ^ 2) (‖x‖ ^ 2) := by
  have hterm : (fun i => ‖(inner ℂ x (d i) : ℂ)‖ ^ 2) =
      (fun i => (inner ℂ x (d i) * inner ℂ (d i) x : ℂ).re) := by
    funext i
    rw [inner_mul_inner_conj_eq_norm_sq, Complex.ofReal_re]
  rw [hterm]
  have hs : HasSum (fun i => (inner ℂ x (d i) * inner ℂ (d i) x : ℂ).re)
      ((inner ℂ x x : ℂ).re) := (d.hasSum_inner_mul_inner x x).mapL Complex.reCLM
  rw [inner_self_eq_norm_sq_to_K] at hs
  exact_mod_cast hs

/-- **`T`'s eigenvector expansion of `x`, applied back through `⟪x, ·⟫`, sums to `⟪x, T x⟫.re`.**
For any `x : H`, `Σₐ (eigenvalue a) * ‖⟪eigenvectorFamily a, x⟫‖² = ⟪x, T x⟫.re`. This is
`hasSum_eigenvectorFamily` (the `tsum` reconstruction `T x = Σₐ ... • eigenvectorFamily a`) pushed
through the continuous, ℝ-linear map `y ↦ ⟪x, y⟫.re`, used pointwise (for `x = d i`, each basis
vector of a Hilbert basis `d`) by `hasSum_inner_apply_eq_trace` below. -/
theorem hasSum_eigen_expansion_inner_apply (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (x : H) :
    HasSum (fun a : EigenvectorIndex T => a.1.1 * ‖(inner ℂ (eigenvectorFamily hT a) x : ℂ)‖ ^ 2)
      (inner ℂ x (T x) : ℂ).re := by
  set e := eigenvectorFamily hT with he_def
  have hs := ((hasSum_eigenvectorFamily hT hT' x).mapL (innerSL ℂ x)).mapL Complex.reCLM
  have heq : (fun a : EigenvectorIndex T => Complex.reCLM ((innerSL ℂ x)
      ((a.1.1 : ℂ) • (inner ℂ (e a) x : ℂ) • e a))) =
      (fun a => a.1.1 * ‖(inner ℂ (e a) x : ℂ)‖ ^ 2) := by
    funext a
    have hstep : (innerSL ℂ x ((a.1.1 : ℂ) • (inner ℂ (e a) x : ℂ) • e a) : ℂ)
        = (a.1.1 : ℂ) * (inner ℂ (e a) x * inner ℂ x (e a) : ℂ) := by
      simp
    change (innerSL ℂ x ((a.1.1 : ℂ) • (inner ℂ (e a) x : ℂ) • e a) : ℂ).re =
      a.1.1 * ‖(inner ℂ (e a) x : ℂ)‖ ^ 2
    rw [hstep, inner_mul_inner_conj_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  rwa [heq] at hs

/-- **`trace` can be computed against *any* Hilbert basis of `H`, not just the eigenbasis used in
its definition.** The basis-independence fact making additive linearity of `trace` provable: two
trace-class self-adjoint compact operators can be compared term-by-term against a *common*
Hilbert basis, sidestepping the fact that their own eigenbases are generally unrelated. Stated as
a genuine `HasSum` (not just a `tsum` equality) so it can be combined additively via
`HasSum.add`. -/
theorem hasSum_inner_apply_eq_trace (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (h : IsTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) (trace h) := by
  classical
  change HasSum (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) (∑' a : EigenvectorIndex T, a.1.1)
  set e := eigenvectorFamily hT with he_def
  set f : EigenvectorIndex T → ι → ℝ :=
    fun a i => a.1.1 * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2 with hf_def
  -- Parseval for `d`, evaluated at each (unit-norm) eigenvector `e a`.
  have hparseval : ∀ a : EigenvectorIndex T, HasSum (fun i => ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2)
      (1 : ℝ) := fun a => by
    have := d.hasSum_norm_sq_inner (e a)
    rwa [(orthonormal_eigenvectorFamily hT hT').1 a, one_pow] at this
  -- Pointwise (for each `d i`), `⟪dᵢ,T(dᵢ)⟩` decomposes as a sum over `EigenvectorIndex T`.
  have hpoint : ∀ i, HasSum (f · i) (inner ℂ (d i) (T (d i)) : ℂ).re :=
    fun i => hasSum_eigen_expansion_inner_apply hT hT' (d i)
  -- The magnitude family is summable over the product index, via trace-class-ness of `T`.
  have hcond1 : ∀ a : EigenvectorIndex T, Summable (fun i => |a.1.1| * ‖(inner ℂ (e a) (d i) :
      ℂ)‖ ^ 2) := fun a => (hparseval a).summable.mul_left _
  have hcond2 : Summable (fun a : EigenvectorIndex T =>
      ∑' i, |a.1.1| * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2) := by
    have heq2 : ∀ a : EigenvectorIndex T,
        ∑' i, |a.1.1| * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2 = |a.1.1| := fun a => by
      rw [tsum_mul_left, (hparseval a).tsum_eq, mul_one]
    have h' : Summable (fun a : EigenvectorIndex T => |a.1.1|) := h
    simpa only [heq2] using h'
  have habs : Summable (fun p : EigenvectorIndex T × ι =>
      |p.1.1.1| * ‖(inner ℂ (e p.1) (d p.2) : ℂ)‖ ^ 2) :=
    (summable_prod_of_nonneg (fun p => by positivity)).mpr ⟨hcond1, hcond2⟩
  have hg : Summable (Function.uncurry f) := by
    have heqabs : (fun p : EigenvectorIndex T × ι => |Function.uncurry f p|) =
        (fun p : EigenvectorIndex T × ι =>
          |p.1.1.1| * ‖(inner ℂ (e p.1) (d p.2) : ℂ)‖ ^ 2) := by
      funext p
      rw [Function.uncurry, hf_def]
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖(inner ℂ (e p.1) (d p.2) : ℂ)‖)]
    exact Summable.of_abs (by rw [heqabs]; exact habs)
  have hpointA : ∀ a : EigenvectorIndex T, HasSum (f a) a.1.1 := fun a => by
    have := (hparseval a).mul_left (a.1.1 : ℝ)
    rwa [mul_one] at this
  have hS_eq : (∑' p, Function.uncurry f p) = ∑' a : EigenvectorIndex T, a.1.1 :=
    (hg.hasSum.prod_fiberwise hpointA).tsum_eq.symm
  have hswap2 : Summable (fun q : ι × EigenvectorIndex T => f q.2 q.1) := hg.prod_symm
  have hHS := hswap2.hasSum.prod_fiberwise hpoint
  have hsymmeq : ∑' q : ι × EigenvectorIndex T, f q.2 q.1 = ∑' p, Function.uncurry f p :=
    (Equiv.prodComm ι (EigenvectorIndex T)).tsum_eq (Function.uncurry f)
  rwa [hsymmeq, hS_eq] at hHS

/-- **Additive linearity of `trace`.** Proved by comparing all three operators against a
*common* Hilbert basis of `H` (via `hasSum_inner_apply_eq_trace`), rather than attempting to
relate `T`'s and `T'`'s individually unrelated eigenbases. -/
theorem trace_add {T' : H →L[ℂ] H} (hT : IsCompactOperator T) (hTsym : T.IsSymmetric)
    (hT' : IsCompactOperator T') (hT'sym : T'.IsSymmetric)
    (hTT' : IsCompactOperator (T + T')) (hTT'sym : (T + T' : H →L[ℂ] H).IsSymmetric)
    (h : IsTraceClass T) (h' : IsTraceClass T') (hsum : IsTraceClass (T + T')) :
    trace hsum = trace h + trace h' := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hs1 := hasSum_inner_apply_eq_trace hT hTsym h d
  have hs2 := hasSum_inner_apply_eq_trace hT' hT'sym h' d
  have hs3 := hasSum_inner_apply_eq_trace hTT' hTT'sym hsum d
  have hadd := hs1.add hs2
  have heq : (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re + (inner ℂ (d i) (T' (d i)) : ℂ).re) =
      (fun i => (inner ℂ (d i) ((T + T') (d i)) : ℂ).re) := by
    funext i
    simp [inner_add_right]
  rw [heq] at hadd
  exact (hadd.unique hs3).symm

/-- **Cyclicity of `trace`.** `trace (S * T') = trace (T' * S)` for self-adjoint compact `S`,
`T'` whose compositions (in both orders) are compact self-adjoint trace-class. Proved via a
*pointwise* identity against a common Hilbert basis, with no order-of-summation swap needed: for
self-adjoint `S`, `⟪dᵢ, S (T' dᵢ)⟫ = ⟪S dᵢ, T' dᵢ⟫` (`IsSymmetric`), and similarly
`⟪dᵢ, T' (S dᵢ)⟫ = ⟪T' dᵢ, S dᵢ⟫`; since `⟪T' dᵢ, S dᵢ⟫` is exactly the complex conjugate of
`⟪S dᵢ, T' dᵢ⟫` (`inner_conj_symm`), the two real parts coincide term by term. -/
theorem trace_comp_comm {T' : H →L[ℂ] H} (_hT : IsCompactOperator T) (hTsym : T.IsSymmetric)
    (_hT' : IsCompactOperator T') (hT'sym : T'.IsSymmetric)
    (hTT' : IsCompactOperator (T * T')) (hTT'sym : (T * T' : H →L[ℂ] H).IsSymmetric)
    (hT'T : IsCompactOperator (T' * T)) (hT'Tsym : (T' * T : H →L[ℂ] H).IsSymmetric)
    (h1 : IsTraceClass (T * T')) (h2 : IsTraceClass (T' * T)) :
    trace h1 = trace h2 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hs1 := hasSum_inner_apply_eq_trace hTT' hTT'sym h1 d
  have hs2 := hasSum_inner_apply_eq_trace hT'T hT'Tsym h2 d
  have heq : (fun i => (inner ℂ (d i) ((T * T') (d i)) : ℂ).re) =
      (fun i => (inner ℂ (d i) ((T' * T) (d i)) : ℂ).re) := by
    funext i
    simp only [mul_apply_eq_comp]
    have h1 : (inner ℂ (d i) (T (T' (d i))) : ℂ) = inner ℂ (T (d i)) (T' (d i)) :=
      (hTsym (d i) (T' (d i))).symm
    have h2 : (inner ℂ (d i) (T' (T (d i))) : ℂ) = inner ℂ (T' (d i)) (T (d i)) :=
      (hT'sym (d i) (T (d i))).symm
    rw [h1, h2]
    have h3 : (inner ℂ (T' (d i)) (T (d i)) : ℂ) =
        starRingEnd ℂ (inner ℂ (T (d i)) (T' (d i))) :=
      (inner_conj_symm (T' (d i)) (T (d i))).symm
    rw [h3, Complex.conj_re]
  rw [heq] at hs1
  exact hs1.unique hs2

/-- **The sum of diagonal matrix elements of a positive trace-class operator against any
orthonormal family is at most its trace.** The family `d` need not be a complete Hilbert basis
of `H` — this is the general fact needed by the Gibbs–Klein / Helmholtz free-energy argument
(`QuantumTheory.TraceClass.helmholtzFreeEnergy_ge`), where `d` is a density operator's own
eigenvector family, generally incomplete (the density operator may have nontrivial kernel).

**Proof idea.** Extend `d` to a full Hilbert basis `b` of `H`
(`Orthonormal.exists_hilbertBasis_extension`, applied to `d.toSubtypeRange`), compute the trace
against `b` (`hasSum_inner_apply_eq_trace`), and compare the sub-family `d` (embedded into `b`'s
index type via the range inclusion) against the full sum, using positivity to control the
(nonneg) terms outside `d`'s range (`hasSum_le_inj`). -/
theorem sum_inner_apply_le_trace {T : H →L[ℂ] H} (hT : IsCompactOperator T)
    (hTsym : T.IsSymmetric) (hTpos : (T : H →ₗ[ℂ] H).IsPositive) (h : IsTraceClass T)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) :
    Summable (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) ∧
      ∑' i, (inner ℂ (d i) (T (d i)) : ℂ).re ≤ trace h := by
  obtain ⟨w, b, hsub, hb_eq⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  set g : w → ℝ := fun j => (inner ℂ (b j) (T (b j)) : ℂ).re with hg_def
  have htr : HasSum g (trace h) := hasSum_inner_apply_eq_trace hT hTsym h b
  have hgnonneg : ∀ j : w, 0 ≤ g j := fun j => hTpos.re_inner_nonneg_right (b j)
  have hd_inj : Function.Injective d := hd.linearIndependent.injective
  set e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩ with he_def
  have he_inj : Function.Injective e := fun i j hij => hd_inj (congrArg Subtype.val hij)
  have hbval : ∀ i, (b (e i) : H) = d i := fun i => by rw [hb_eq]
  set fι : ι → ℝ := fun i => (inner ℂ (d i) (T (d i)) : ℂ).re with hf_def
  have hge : ∀ i, g (e i) = fι i := fun i => by
    change (inner ℂ (b (e i)) (T (b (e i))) : ℂ).re = fι i
    rw [hbval i]
  have hgsum : Summable g := htr.summable
  have hsub_sum : Summable (fun x : Set.range e => g x) := hgsum.subtype _
  set hphi := Equiv.ofInjective e he_inj with hphi_def
  have heq : (fun x : Set.range e => g x) ∘ hphi = fι := by
    funext i
    change g (hphi i : w) = fι i
    have hcoe : (hphi i : w) = e i := rfl
    rw [hcoe]; exact hge i
  have hfsum : Summable fι := by
    rw [← heq]
    exact hphi.summable_iff.mpr hsub_sum
  refine ⟨hfsum, ?_⟩
  exact hasSum_le_inj e he_inj (fun c _ => hgnonneg c)
    (fun i => le_of_eq (hge i).symm) hfsum.hasSum htr

end ContinuousLinearMap
