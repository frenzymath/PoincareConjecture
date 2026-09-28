import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.InfiniteRatio
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ZeroVolume.Induction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem zero_asymptoticVolumeRatio_of_bounded_ancient
    {n : ℕ} (hn : 2 ≤ n) {M : Type u}
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hnonflat : ∃ q, 0 < (F.connection 0).scalarCurvature q) :
    ∀ t ≤ 0, ∀ p : M, (F.metric t).asymptoticVolumeRatio p = 0 ∧
      Tendsto (fun r : ℝ =>
        ((F.metric t).volumeMeasure ((F.metric t).ball p r)).toReal / r ^ n)
        atTop (𝓝 0) := by
  apply zero_volume_of_unbounded_scalar_ratio_in_all_dimensions hC ?_ hn F
    hcomplete hoperator hK hbound hκ hnoncollapse hnonflat
  intro d hd C hNC G hc hop K hK hb κ hκ hcollapse hflat t ht p hbounded
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let : NoncompactSpace C.carrier := hNC
  obtain ⟨A, hA⟩ := hbounded
  obtain ⟨x, _, hx⟩ := G.infinite_scalar_ratio_of_bounded_ancient hd hC hc hop
    hK hb hflat hκ hcollapse t ht.le p 0 A
  have hle := hA (mem_range_self x)
  exact (not_lt_of_ge hle) (by simpa only [mul_comm] using hx)

end PoincareConjecture.RicciFlow
