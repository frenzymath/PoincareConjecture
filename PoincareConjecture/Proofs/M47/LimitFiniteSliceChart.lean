import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalChart
import PoincareConjecture.Proofs.M47.LimitNoncollapsePhysicalTime









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance sliceChartTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance sliceChartCharts :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance sliceChartManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold


noncomputable def limitFiniteSliceTime (t : ℝ) (k : ℕ) : ℝ :=
  if t ∈ Icc (-G.exhaustion.time k) 0 then t else 0


theorem limitFinite_slice_time_mem (t : ℝ) (k : ℕ) :
    limitFiniteSliceTime G t k ∈ Icc (-G.exhaustion.time k) 0 := by
  classical
  unfold limitFiniteSliceTime
  split_ifs with ht
  · exact ht
  · exact ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩


theorem limitFinite_slice_time_eventually_eq (t : ℝ) (ht : t ∈ J) :
    ∀ᶠ k : ℕ in atTop, limitFiniteSliceTime G t k = t := by
  filter_upwards [G.exhaustion.time_cofinal {t} isCompact_singleton
    (singleton_subset_iff.mpr ht)] with k hk
  exact if_pos (hk (mem_singleton t))


noncomputable def limitFinitePhysicalSliceTime (t : ℝ) (k : ℕ) : ℝ :=
  (V.base (G.subsequence k)).1 + limitFiniteSliceTime G t k / V.scale (G.subsequence k)


theorem limitFinite_physical_slice_time_mem (t : ℝ) (k : ℕ) :
    limitFinitePhysicalSliceTime G t k ∈ (V.flow (G.subsequence k)).interval :=
  limitNoncollapse_physical_time_mem G k (limitFiniteSliceTime G t k)
    (limitFinite_slice_time_mem G t k)



noncomputable def limitFinitePhysicalSliceChart
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i)) (t : ℝ) (k : ℕ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.sliceCarrier.carrier
      ((F (G.subsequence k)).slice (limitFinitePhysicalSliceTime G t k)).carrier ∞ :=
  limitCanonicalPhysicalChart (G.embedding k) (G.exhaustion.space_open k)
    (R (G.subsequence k)) (limitFiniteSliceTime G t k)
    (limitFinite_slice_time_mem G t k) (limitFinite_physical_slice_time_mem G t k)


theorem limitFinite_physical_slice_chart_source
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i)) (t : ℝ) (k : ℕ) :
    (limitFinitePhysicalSliceChart G F R t k).source = G.exhaustion.space k :=
  limitCanonicalPhysicalChart_source (G.embedding k) (G.exhaustion.space_open k)
    (R (G.subsequence k)) (limitFiniteSliceTime G t k)
    (limitFinite_slice_time_mem G t k) (limitFinite_physical_slice_time_mem G t k)

end PoincareConjecture.M47
