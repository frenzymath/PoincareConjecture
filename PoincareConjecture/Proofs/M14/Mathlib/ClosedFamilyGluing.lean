import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set Filter
open scoped Manifold Topology

namespace PoincareConjecture.M14

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  (IM : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffOn_union_closed_tubes {k : WithTop ℕ∞} {U : Set E} {a l c d : ℝ}
    (hlc : l < c) {f : E × ℝ → M}
    (hleft : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) IM k f (U ×ˢ Icc a c))
    (hright : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) IM k f (U ×ˢ Icc l d)) :
    ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) IM k f (U ×ˢ Icc a d) := by
  intro z hz
  by_cases hzc : z.2 < c
  · apply (hleft z ⟨hz.1, hz.2.1, hzc.le⟩).mono_of_mem_nhdsWithin
    have hnear : {w : E × ℝ | w.2 < c} ∈ 𝓝 z :=
      (isOpen_Iio.preimage continuous_snd).mem_nhds hzc
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with w hw hdom
    exact ⟨hdom.1, hdom.2.1, hw.le⟩
  · have hlz : l < z.2 := hlc.trans_le (le_of_not_gt hzc)
    apply (hright z ⟨hz.1, hlz.le, hz.2.2⟩).mono_of_mem_nhdsWithin
    have hnear : {w : E × ℝ | l < w.2} ∈ 𝓝 z :=
      (isOpen_Ioi.preimage continuous_snd).mem_nhds hlz
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with w hw hdom
    exact ⟨hdom.1, hw.le, hdom.2.2⟩

end PoincareConjecture.M14
