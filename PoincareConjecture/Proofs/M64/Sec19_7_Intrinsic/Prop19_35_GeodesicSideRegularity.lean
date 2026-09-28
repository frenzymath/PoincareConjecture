import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicSideNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryMetricSegment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.MetricArc

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ENNReal Manifold ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_constrained_minimizer_geodesic_side
    (G : RiemannianMetric 2 AnnulusCoordinates) {K C : Set AnnulusCoordinates}
    (hK : IsClosed K) (hC : IsCompact C)
    {alpha : ℝ → AnnulusCoordinates} {a b p : ℝ}
    (hc : ContinuousOn alpha (Icc a b)) (hinj : InjOn alpha (Icc a b))
    (hgeo : G.IsGeodesicOn alpha (Ioo a b)) (hp : p ∈ Ioo a b)
    (hfront : frontier K ⊆ alpha '' Icc a b ∪ C)
    (hside : MapsTo alpha (Icc a b) K) (hpC : alpha p ∉ C)
    {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hconf : MapsTo gamma (Icc 0 L) K)
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ c ∈ Icc 0 L, ∀ d ∈ Icc 0 L, c ≤ d →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma c → tau 1 = gamma d → MapsTo tau (Icc 0 1) K →
        ENNReal.ofReal (d - c) ≤ m64IntrinsicCurveVariation G tau 0 1)
    {u : ℝ} (hu : u ∈ Ioo 0 L) (hpoint : gamma u = alpha p) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ Icc (u - epsilon) (u + epsilon) ⊆ Icc 0 L ∧
      G.IsGeodesicOn gamma (Ioo (u - epsilon) (u + epsilon)) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ gamma (Ioo (u - epsilon) (u + epsilon)) := by
  obtain ⟨O, hO, hpO, hconnect⟩ :=
    m64Intrinsic_exists_geodesic_side_frontier_connectors G hc hinj hgeo hp
      hfront hside hC hpC
  obtain ⟨epsilon, hepsilon, hJ, hmetric⟩ :=
    m64Intrinsic_constrained_minimizer_metric_segment_of_frontier_connectors
      G hK hconf hlip hmin hu (by rw [hpoint]; exact hO.mem_nhds hpO) hconnect
  obtain ⟨hgamma, hsmooth⟩ := G.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment
    (γ := gamma) (a := u - epsilon) (b := u + epsilon) (c := 1) zero_le_one (by
      intro s hs t ht
      simpa only [one_mul] using hmetric s (Ioo_subset_Icc_self hs) t (Ioo_subset_Icc_self ht))
  exact ⟨epsilon, hepsilon, hJ, hgamma, hsmooth⟩

end PoincareConjecture
