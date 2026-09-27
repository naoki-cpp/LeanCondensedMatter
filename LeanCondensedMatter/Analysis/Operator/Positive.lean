import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive continuous linear maps

General closure properties for positive bounded operators that are not yet exposed directly by
Mathlib.
-/

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Positivity is closed under convergence in the continuous-linear-map topology. -/
theorem isPositive_of_tendsto
    {α : Type*} {l : Filter α} [NeBot l]
    {F : α → H →L[𝕜] H} {T : H →L[𝕜] H}
    (hF : Tendsto F l (𝓝 T)) (hpos : ∀ᶠ i in l, (F i).IsPositive) : T.IsPositive := by
  rw [isPositive_iff]
  constructor
  · intro x y
    have happly_x : Tendsto (fun i => F i x) l (𝓝 (T x)) :=
      ((apply 𝕜 H x).continuous.tendsto T).comp hF
    have happly_y : Tendsto (fun i => F i y) l (𝓝 (T y)) :=
      ((apply 𝕜 H y).continuous.tendsto T).comp hF
    have hleft : Tendsto (fun i => inner 𝕜 (F i x) y) l (𝓝 (inner 𝕜 (T x) y)) :=
      happly_x.inner tendsto_const_nhds
    have hright : Tendsto (fun i => inner 𝕜 x (F i y)) l (𝓝 (inner 𝕜 x (T y))) :=
      tendsto_const_nhds.inner happly_y
    have heq : ∀ᶠ i in l, inner 𝕜 (F i x) y = inner 𝕜 x (F i y) :=
      hpos.mono fun i hi => hi.isSymmetric x y
    have hright' : Tendsto (fun i => inner 𝕜 (F i x) y) l (𝓝 (inner 𝕜 x (T y))) :=
      (tendsto_congr' heq).mpr hright
    exact tendsto_nhds_unique hleft hright'
  · intro x
    have happly : Tendsto (fun i => F i x) l (𝓝 (T x)) :=
      ((apply 𝕜 H x).continuous.tendsto T).comp hF
    have hinner :
        Tendsto (fun i => RCLike.re (inner 𝕜 (F i x) x)) l
          (𝓝 (RCLike.re (inner 𝕜 (T x) x))) :=
      RCLike.continuous_re.continuousAt.tendsto.comp
        (happly.inner tendsto_const_nhds)
    exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto hinner
      (hpos.mono fun i hi => hi.re_inner_nonneg_left x)

end ContinuousLinearMap
