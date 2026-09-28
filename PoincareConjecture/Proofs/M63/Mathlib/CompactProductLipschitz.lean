import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M63

theorem exists_lipschitzOnWith_compact_product
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {J : Set E} (hJ : Convex ℝ J) {U : Set F} (hU : IsOpen U)
    {f : E × F → G} (hf : ContDiffOn ℝ 1 f (J ×ˢ U))
    {K : Set (E × F)} (hK : IsCompact K) (hKU : K ⊆ J ×ˢ U) :
    ∃ L : NNReal, LipschitzOnWith L f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro p hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p.2 (hKU hp).2
  let D := J ×ˢ ball p.2 ε
  have hDsub : D ⊆ J ×ˢ U := fun _ hx => ⟨hx.1, hball hx.2⟩
  have hpD : p ∈ D := ⟨(hKU hp).1, mem_ball_self hε⟩
  obtain ⟨L, N, hN, hLip⟩ := (hf.mono hDsub p hpD).exists_lipschitzOnWith
    (hJ.prod (convex_ball p.2 ε))
  have hDK : D ∈ 𝓝[K] p := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (continuous_snd.tendsto p (ball_mem_nhds p.2 hε))]
      with q hq hqball
    exact ⟨(hKU hq).1, hqball⟩
  exact ⟨L, N, (nhdsWithin_le_of_mem hDK) hN, hLip⟩

end PoincareConjecture.M63
