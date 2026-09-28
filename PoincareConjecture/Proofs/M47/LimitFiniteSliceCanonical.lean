import PoincareConjecture.Proofs.M47.LimitFiniteSliceChart
import PoincareConjecture.Proofs.M47.LimitNoncollapsePointScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (blowupBackwardInterval H))

private local instance sliceCanonicalTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance sliceCanonicalCharts :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance sliceCanonicalManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem limitFinite_eventually_physical_slice_canonical
    (P : M47Predecessors.{u}) (hfinite : H ≠ ⊤) {epsilon C : ℝ}
    (hParameters : ∀ k, (F k).parameters.epsilon = epsilon ∧ (F k).parameters.C = C)
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) (htneg : t < 0)
    (x : G.limit.sliceCarrier.carrier) (hx : 1 < (G.limit.flow.connection t).scalarCurvature x) :
    ∀ᶠ k : ℕ in atTop,
      SurgeryCanonicalControl (F (G.subsequence k)) (limitFinitePhysicalSliceTime G t k)
        (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) epsilon C := by
  have hscalar := limitNoncollapse_eventually_point_scalar G P t ht x
    (show 0 < ((G.limit.flow.connection t).scalarCurvature x - 1) / 2 by linarith)
  have htime := limitNoncollapse_eventually_physical_time_pos hfinite G
    (fun k => regular_history_interval_nonnegative (history k)) t ht
  filter_upwards [hscalar, htime, limitFinite_slice_time_eventually_eq G t ht]
    with k hkscalar hktime hkeq
  let q := (V).scale (G.subsequence k)
  have hq : 0 < q := (V).base_scalar_pos (G.subsequence k)
  have hread :
      ((F (G.subsequence k)).connection (limitFinitePhysicalSliceTime G t k)).scalarCurvature
        (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) =
      ((V).flow (G.subsequence k)).scalar ((G.embedding k).pointMap
        (limitFiniteSliceTime G t k) (limitFinite_slice_time_mem G t k) x) :=
    (history (G.subsequence k)).scalar_pullback _
      (limitFinite_physical_slice_time_mem G t k) _
  have herr :
      |((V).flow (G.subsequence k)).scalar ((G.embedding k).pointMap
        (limitFiniteSliceTime G t k) (limitFinite_slice_time_mem G t k) x) / q -
          (G.limit.flow.connection t).scalarCurvature x| <
            ((G.limit.flow.connection t).scalarCurvature x - 1) / 2 := by
    simpa only [hkeq] using hkscalar.2.2 hkscalar.1
  rw [← hread] at herr
  have hnormalized : 1 ≤
      ((F (G.subsequence k)).connection (limitFinitePhysicalSliceTime G t k)).scalarCurvature
        (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) / q := by
    linarith [(abs_lt.mp herr).1]
  have hfloor : (rNext (G.subsequence k))⁻¹ ^ 2 ≤
      ((F (G.subsequence k)).connection (limitFinitePhysicalSliceTime G t k)).scalarCurvature
        (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) :=
    (hThreshold (G.subsequence k)).trans (by
      simpa only [one_mul] using (le_div_iff₀ hq).mp hnormalized)
  have hpos : 0 < limitFinitePhysicalSliceTime G t k := by
    simpa only [limitFinitePhysicalSliceTime, hkeq] using hktime.2.2
  have hpast : limitFinitePhysicalSliceTime G t k < baseTime (G.subsequence k) := by
    change baseTime (G.subsequence k) + limitFiniteSliceTime G t k / q < _
    rw [hkeq]
    linarith [div_neg_of_neg_of_pos htneg hq]
  simpa only [(hParameters (G.subsequence k)).1, (hParameters (G.subsequence k)).2] using
    hEarlier (G.subsequence k) (limitFinitePhysicalSliceTime G t k) ⟨hpos.le, hpast⟩
      ((history (G.subsequence k)).history.time_subset (limitFinite_physical_slice_time_mem G t k))
      (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) hfloor

end PoincareConjecture.M47
