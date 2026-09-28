import PoincareConjecture.Proofs.M47.LimitFiniteSliceChart
import PoincareConjecture.Proofs.M47.LimitNoncollapseUniformCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

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

private local instance anchorBoundsTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance anchorBoundsCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance anchorBoundsManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem limitFinite_eventually_physical_anchor_bounds
    (P : M47Predecessors.{u}) (t : ℝ) (ht : t ∈ blowupBackwardInterval H)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) {B : ℝ}
    (hB : ∀ x ∈ K, (G.limit.flow.connection t).curvatureTensorNorm x < B) :
    ∀ᶠ k : ℕ in atTop,
      limitFiniteSliceTime G t k = t ∧ K ⊆ G.exhaustion.space k ∧
      ∀ x ∈ K,
        ((F (G.subsequence k)).connection (limitFinitePhysicalSliceTime G t k)).curvatureTensorNorm
            (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) <
          B * (V).scale (G.subsequence k) ∧
        ((F (G.subsequence k)).connection (limitFinitePhysicalSliceTime G t k)).scalarCurvature
            (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) <
          (3 * B) * (V).scale (G.subsequence k) := by
  have hbound := limitNoncollapse_generalized_compact_curvature_lt G P
    isCompact_singleton (singleton_subset_iff.mpr ht) hK
    (fun s hs x hx => mem_singleton_iff.mp hs ▸ hB x hx)
  filter_upwards [hbound, limitFinite_slice_time_eventually_eq G t ht]
    with k hk htime
  refine ⟨htime, hk.2.1, ?_⟩
  intro x hx
  have hread :
      ((F (G.subsequence k)).connection (limitFinitePhysicalSliceTime G t k)).curvatureTensorNorm
        (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) =
      ((V).flow (G.subsequence k)).curvatureNorm ((G.embedding k).pointMap
        (limitFiniteSliceTime G t k) (limitFinite_slice_time_mem G t k) x) :=
    (history (G.subsequence k)).curvature_norm_pullback _
      (limitFinite_physical_slice_time_mem G t k) _
  have hnorm :
      ((F (G.subsequence k)).connection (limitFinitePhysicalSliceTime G t k)).curvatureTensorNorm
        (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x) <
          B * (V).scale (G.subsequence k) := by
    rw [hread]
    apply (div_lt_iff₀ ((V).base_scalar_pos (G.subsequence k))).mp
    exact hk.2.2 _ (by simpa only [htime] using mem_singleton t)
      (limitFinite_slice_time_mem G t k) x hx
  refine ⟨hnorm, ?_⟩
  have hscalar := ((F (G.subsequence k)).connection
    (limitFinitePhysicalSliceTime G t k)).scalarCurvature_le_curvatureTensorNorm_sharp
      (limitFinitePhysicalSliceChart G F (fun i => (history i).history) t k x)
  norm_num only [Nat.cast_ofNat] at hscalar
  nlinarith only [hscalar, hnorm]

end PoincareConjecture.M47
