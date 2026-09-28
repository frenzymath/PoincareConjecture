import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Instances.Real.Lemmas









set_option autoImplicit false

open Set Filter
open scoped Manifold Topology

namespace PoincareConjecture.M14

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (IM : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]




theorem contMDiffOn_paste_closed_intervals {k : WithTop ℕ∞} {a l c r : ℝ}
    (hlc : l < c) {f g : ℝ → M}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ)) IM k f (Icc a c))
    (hg : ContMDiffOn (𝓘(ℝ, ℝ)) IM k g (Icc l r))
    (heq : EqOn f g (Icc l c)) :
    ContMDiffOn (𝓘(ℝ, ℝ)) IM k (fun s => if s ≤ c then f s else g s) (Icc a r) := by
  have hleft : EqOn (fun s => if s ≤ c then f s else g s) f (Icc a c) :=
    fun s hs => if_pos hs.2
  have hright : EqOn (fun s => if s ≤ c then f s else g s) g (Icc l r) := by
    intro s hs
    by_cases hsc : s ≤ c
    · exact (if_pos hsc).trans (heq ⟨hs.1, hsc⟩)
    · exact if_neg hsc
  intro s hs
  by_cases hsc : s < c
  · have hsold : s ∈ Icc a c := ⟨hs.1, hsc.le⟩
    apply ((hf s hsold).congr_of_mem hleft hsold).mono_of_mem_nhdsWithin
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Iio c, Iio_mem_nhds hsc, fun _ ht => ⟨ht.2.1, ht.1.le⟩⟩
  · have hcs : c ≤ s := le_of_not_gt hsc
    have hsnew : s ∈ Icc l r := ⟨hlc.le.trans hcs, hs.2⟩
    apply ((hg s hsnew).congr_of_mem hright hsnew).mono_of_mem_nhdsWithin
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Ioi l, Ioi_mem_nhds (hlc.trans_le hcs), fun _ ht => ⟨ht.1.le, ht.2.2⟩⟩

end PoincareConjecture.M14
