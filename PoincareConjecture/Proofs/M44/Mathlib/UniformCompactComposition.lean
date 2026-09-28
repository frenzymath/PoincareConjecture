import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

theorem ContinuousOn.comp_tendstoUniformlyOn_of_compact_image
    {P E F ι : Type*} [MetricSpace E] [LocallyCompactSpace E] [UniformSpace F]
    {l : Filter ι} {fseq : ι → P → E} {f : P → E} {s : Set P}
    {g : E → F} {U : Set E} (hg : ContinuousOn g U) (hU : IsOpen U)
    (hf : IsCompact (f '' s)) (hfU : MapsTo f s U)
    (hconv : TendstoUniformlyOn fseq f l s) :
    TendstoUniformlyOn (fun i x => g (fseq i x)) (fun x => g (f x)) l s := by
  obtain ⟨K, hK, hfK, hKU⟩ := exists_compact_between hf hU (image_subset_iff.mpr hfU)
  obtain ⟨delta, hdelta, hthick⟩ := hf.exists_cthickening_subset_open isOpen_interior hfK
  have hseqK : ∀ᶠ i in l, ∀ x ∈ s, fseq i x ∈ K := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv delta hdelta] with i hi
    intro x hx
    apply interior_subset (hthick ?_)
    exact mem_cthickening_of_dist_le (fseq i x) (f x) delta (f '' s)
      (mem_image_of_mem f hx) (by simpa only [dist_comm] using (hi x hx).le)
  exact (hK.uniformContinuousOn_of_continuous (hg.mono hKU)).comp_tendstoUniformlyOn_eventually
    hseqK (fun x hx => interior_subset (hfK (mem_image_of_mem f hx))) hconv
