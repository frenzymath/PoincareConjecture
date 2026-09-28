import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Confinement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Ellipticity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.TransitionBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

theorem locallyEventuallyBoundedDerivatives_relativeCoordinateMap
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    (hmetric : ∀ k, (F (G.subsequence k)).metricAt 0 = (H (L.subsequence k)).metricAt 0)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (f : G.limitCarrier.carrier → L.limitCarrier.carrier) (hf : Continuous f)
    (hconv : letI := (L.limitFlow.metricAt 0).toMetricSpace
      ∀ Q : Set G.limitCarrier.carrier, IsCompact Q →
        TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) f atTop Q)
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier) :
    LocallyEventuallyBoundedDerivatives (G.relativeCoordinateDomain L f qG qL)
      (fun k ↦ G.relativeCoordinateMap L qG qL (σ k)) := by
  let := (G.limitFlow.metricAt 0).toMetricSpace
  let := (L.limitFlow.metricAt 0).toMetricSpace
  intro Q hQ hQΩ m
  obtain ⟨K, hK, hQK, hKΩ⟩ := exists_compact_between hQ
    (G.isOpen_relativeCoordinateDomain L f hf qG qL) hQΩ
  have hKc : K ⊆ (extChartAt (𝓡 n) qG).target := fun _ hx ↦ (hKΩ hx).1
  have hKimage := hK.image_of_continuousOn
    ((contMDiffOn_extChartAt_symm (n := ∞) qG).continuousOn.mono hKc)
  obtain ⟨r₀, hKr₀⟩ := hKimage.isBounded.subset_ball G.limitFlow.base
  let r := max r₀ 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKr : (extChartAt (𝓡 n) qG).symm '' K ⊆ Metric.ball G.limitFlow.base r :=
    hKr₀.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hKr' : MapsTo (extChartAt (𝓡 n) qG).symm K (G.limitFlow.ballAt 0 r) := by
    intro y hy
    change (extChartAt (𝓡 n) qG).symm y ∈
      (G.limitFlow.metricAt 0).ball G.limitFlow.base r
    rw [← (G.limitFlow.metricAt 0).toMetricSpace_ball]
    exact hKr (mem_image_of_mem _ hy)
  obtain ⟨T, hT, hTc, htarget⟩ := G.exists_compact_relativeCoordinate_target L f hf hconv
    qG qL hK hKΩ
  obtain ⟨U, hU, hKU, hUc⟩ := exists_compact_between hK
    (isOpen_extChartAt_target (I := 𝓡 n) qG) hKc
  obtain ⟨V, hV, hTV, hVc⟩ := exists_compact_between hT
    (isOpen_extChartAt_target (I := 𝓡 n) qL) hTc
  have hA : ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (G.pulledChartCoefficients qG (σ k) 0) (interior U) := by
    filter_upwards [hσ.tendsto_atTop.eventually
      (G.eventually_contDiffAt_pulledChartCoefficients_on_compact qG 0 hGtime U hU hUc)]
      with k hk y hy
    exact (hk y (interior_subset hy)).contDiffWithinAt
  have hB : ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (L.pulledChartCoefficients qL (σ k) 0) (interior V) := by
    filter_upwards [hσ.tendsto_atTop.eventually
      (L.eventually_contDiffAt_pulledChartCoefficients_on_compact qL 0 hLtime V hV hVc)]
      with k hk y hy
    exact (hk y (interior_subset hy)).contDiffWithinAt
  have hAb : LocallyEventuallyBoundedDerivatives (interior U)
      (fun k ↦ G.pulledChartCoefficients qG (σ k) 0) := by
    intro R hR hRU l
    obtain ⟨D, hD⟩ := G.locallyEventuallyBoundedDerivatives_pulledChartCoefficients
      qG 0 hGtime R hR (hRU.trans (interior_subset.trans hUc)) l
    exact ⟨D, hσ.tendsto_atTop.eventually hD⟩
  have hBb : LocallyEventuallyBoundedDerivatives (interior V)
      (fun k ↦ L.pulledChartCoefficients qL (σ k) 0) := by
    intro R hR hRV l
    obtain ⟨D, hD⟩ := L.locallyEventuallyBoundedDerivatives_pulledChartCoefficients
      qL 0 hLtime R hR (hRV.trans (interior_subset.trans hVc)) l
    exact ⟨D, hσ.tendsto_atTop.eventually hD⟩
  obtain ⟨α, hα, hAlow⟩ := G.eventually_uniformEllipticity_pulledChartCoefficients
    qG 0 hGtime K hK hKc
  obtain ⟨β, hβ, hBlow⟩ := L.eventually_uniformEllipticity_pulledChartCoefficients
    qL 0 hLtime T hT hTc
  obtain ⟨j, hj⟩ := L.exists_exhaustion_superset
    ((L.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hLcomplete
      L.limitFlow.base (4 * r))
  have hrelative : ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (G.relativeCoordinateMap L qG qL (σ k)) (interior K) ∧
      ∀ y ∈ interior K, ∀ v w,
        L.pulledChartCoefficients qL (σ k) 0 (G.relativeCoordinateMap L qG qL (σ k) y)
          (fderiv ℝ (G.relativeCoordinateMap L qG qL (σ k)) y v)
          (fderiv ℝ (G.relativeCoordinateMap L qG qL (σ k)) y w) =
        G.pulledChartCoefficients qG (σ k) 0 y v w := by
    filter_upwards [hσ.tendsto_atTop.eventually (eventually_relative_map_smooth C F H G L
        hGtime hLtime hGcomplete hLcomplete hsource hr),
      hσ.tendsto_atTop.eventually (eventually_ge_atTop j), htarget]
      with k hk hjk hkt
    apply G.relativeCoordinateMap_smooth_pullback_on L qG qL (σ k) hLtime (hmetric _)
      isOpen_interior (interior_subset.trans hKc)
    intro y hy
    have hyr := hKr' (interior_subset hy)
    exact ⟨hk.2.1 _ hyr,
      L.exhaustion_monotone hjk (hj (subset_closure (hk.1 hyr))),
      hkt.2 y (interior_subset hy), hk.2.2 _ hyr⟩
  obtain ⟨D, hD⟩ := CoordinateTransition.eventually_derivative_bounds_of_eventually_smooth_metrics
    isOpen_interior isOpen_interior hK hT hKU hTV hA hB hAb hBb
    (fun k x _ v w ↦ ((F (G.subsequence (σ k))).metricAt 0).symm _ _ _)
    (fun k x _ v w ↦ ((H (L.subsequence (σ k))).metricAt 0).symm _ _ _)
    ⟨α, hα, hσ.tendsto_atTop.eventually hAlow⟩
    ⟨β, hβ, hσ.tendsto_atTop.eventually hBlow⟩
    (hrelative.mono fun _ hk ↦ hk.1)
    (htarget.mono fun _ hk _ hx ↦ hk.1 (interior_subset hx))
    (hrelative.mono fun _ hk ↦ hk.2) m
  exact ⟨D, hD.mono fun _ hk x hx ↦ hk x (hQK hx)⟩

end PoincareConjecture.PointedGeometricConvergence
