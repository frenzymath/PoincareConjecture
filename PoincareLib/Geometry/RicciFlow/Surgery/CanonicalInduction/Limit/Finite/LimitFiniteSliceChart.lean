import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalPhysicalChart
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Noncollapse.LimitNoncollapsePhysicalTime

/-!
# The original physical charts at a fixed included limit time

Zero totalizes only the unavailable prefix. Cofinality keeps the fixed
time on one original tail, with no change to the selected subsequence.
MT Proposition 17.1; limit-finite-slice-readout.md, B.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance sliceChartTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance sliceChartCharts :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance sliceChartManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

/-- The fixed normalized time on every available source cylinder. -/
noncomputable def limitFiniteSliceTime (t : ℝ) (k : ℕ) : ℝ :=
  if t ∈ Icc (-G.exhaustion.time k) 0 then t else 0

/-- The totalized time is included for every original source index. -/
theorem limitFinite_slice_time_mem (t : ℝ) (k : ℕ) :
    limitFiniteSliceTime G t k ∈ Icc (-G.exhaustion.time k) 0 := by
  classical
  unfold limitFiniteSliceTime
  split_ifs with ht
  · exact ht
  · exact ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩

/-- The totalization agrees with the requested time on one original tail. -/
theorem limitFinite_slice_time_eventually_eq (t : ℝ) (ht : t ∈ J) :
    ∀ᶠ k : ℕ in atTop, limitFiniteSliceTime G t k = t := by
  filter_upwards [G.exhaustion.time_cofinal {t} isCompact_singleton
    (singleton_subset_iff.mpr ht)] with k hk
  exact if_pos (hk (mem_singleton t))

/-- The actual physical clock of the unchanged selected cylinder. -/
noncomputable def limitFinitePhysicalSliceTime (t : ℝ) (k : ℕ) : ℝ :=
  (V.base (G.subsequence k)).1 + limitFiniteSliceTime G t k / V.scale (G.subsequence k)

/-- An actual cylinder point supplies membership of the physical clock. -/
theorem limitFinite_physical_slice_time_mem (t : ℝ) (k : ℕ) :
    limitFinitePhysicalSliceTime G t k ∈ (V.flow (G.subsequence k)).interval :=
  limitNoncollapse_physical_time_mem G k (limitFiniteSliceTime G t k)
    (limitFinite_slice_time_mem G t k)

/-- The physical chart is the same cylinder map followed by the same
regular-history realization at its literal included clock. -/
noncomputable def limitFinitePhysicalSliceChart
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i)) (t : ℝ) (k : ℕ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.sliceCarrier.carrier
      ((F (G.subsequence k)).slice (limitFinitePhysicalSliceTime G t k)).carrier ∞ :=
  limitCanonicalPhysicalChart (G.embedding k) (G.exhaustion.space_open k)
    (R (G.subsequence k)) (limitFiniteSliceTime G t k)
    (limitFinite_slice_time_mem G t k) (limitFinite_physical_slice_time_mem G t k)

/-- Physical composition preserves the entire original exhaustion stage. -/
theorem limitFinite_physical_slice_chart_source
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i)) (t : ℝ) (k : ℕ) :
    (limitFinitePhysicalSliceChart G F R t k).source = G.exhaustion.space k :=
  limitCanonicalPhysicalChart_source (G.embedding k) (G.exhaustion.space_open k)
    (R (G.subsequence k)) (limitFiniteSliceTime G t k)
    (limitFinite_slice_time_mem G t k) (limitFinite_physical_slice_time_mem G t k)

end PoincareMT.M47
