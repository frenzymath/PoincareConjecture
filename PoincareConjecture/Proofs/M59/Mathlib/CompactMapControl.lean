import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor










set_option autoImplicit false

open Set Metric
open scoped Topology

namespace PoincareConjecture.Proofs.M59




theorem exists_uniform_compact_map_control
    {A B : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    (f : A → B) {S U : Set A} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hf : ∀ a ∈ S, ContinuousAt f a) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ delta > 0, ∀ a ∈ S, ∀ z, dist z a < delta →
      z ∈ U ∧ dist (f z) (f a) < epsilon := by
  obtain ⟨d1, hd1, hsubset⟩ := hS.exists_thickening_subset_open hU hSU
  obtain ⟨d2, hd2, hcontrol⟩ := Metric.mem_uniformity_dist.mp
    (hS.uniformContinuousAt_of_continuousAt f hf (Metric.dist_mem_uniformity he))
  refine ⟨min d1 d2, lt_min hd1 hd2, ?_⟩
  intro a ha z hz
  refine ⟨hsubset (Metric.mem_thickening_iff.mpr ⟨a, ha, hz.trans_le (min_le_left _ _)⟩), ?_⟩
  have h := hcontrol (a := a) (b := z)
    (by simpa only [dist_comm] using hz.trans_le (min_le_right _ _)) ha
  change dist (f a) (f z) < epsilon at h
  simpa only [dist_comm] using h

end PoincareConjecture.Proofs.M59
