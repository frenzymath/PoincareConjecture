import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology



theorem hasFTaylorSeriesUpTo_of_compact_uniform_jet_limits
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {l : Filter ι} [NeBot l] {f : ι → E → F}
    {p : E → FormalMultilinearSeries 𝕜 E F}
    (hf : ∀ i, ContDiff 𝕜 ∞ (f i))
    (hconv : ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun i => iteratedFDeriv 𝕜 m (f i)) (fun x => p x m) l K) :
    HasFTaylorSeriesUpTo ∞ (fun x => (p x 0).curry0) p := by
  apply (hasFTaylorSeriesUpTo_top_iff' le_rfl).mpr
  refine ⟨fun _ => rfl, ?_⟩
  intro m x
  let e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) => E) F
  have hnext := e.isometry.uniformContinuous.comp_tendstoUniformlyOn
    (hconv (m + 1) (Metric.closedBall x 1) (isCompact_closedBall x 1))
  apply hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball
    (hnext.mono Metric.ball_subset_closedBall)
  · intro i y _hy
    have hd := ((hf i).differentiable_iteratedFDeriv (m := m)
      (by exact_mod_cast ENat.natCast_lt_top m) y).hasFDerivAt
    convert! hd using 1
  · intro y _hy
    exact (hconv m {y} isCompact_singleton).tendsto_at (mem_singleton y)
  · exact Metric.mem_ball_self zero_lt_one
