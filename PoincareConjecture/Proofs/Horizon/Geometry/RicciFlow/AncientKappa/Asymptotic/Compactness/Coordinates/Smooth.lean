import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.DerivativeBounds
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Uniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

variable {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
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
    (qG : G.limitCarrier.carrier) (qL : L.limitCarrier.carrier)

include hconv in
theorem tendsto_relativeCoordinateMap
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ G.relativeCoordinateDomain L f qG qL) :
    Tendsto (fun k ↦ G.relativeCoordinateMap L qG qL (σ k) y) atTop
      (𝓝 (extChartAt (𝓡 n) qL (f ((extChartAt (𝓡 n) qG).symm y)))) := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  have hpoint := (hconv {(extChartAt (𝓡 n) qG).symm y} isCompact_singleton).tendsto_at
    (mem_singleton _)
  have hc := (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := qL)).continuousOn.continuousAt
    (by simpa only [extChartAt_source] using
      (isOpen_extChartAt_source (I := 𝓡 n) qL).mem_nhds hy.2)
  exact hc.tendsto.comp hpoint

include hGtime hLtime hGcomplete hLcomplete hsource hσ hf hconv in
theorem eventually_contDiffOn_relativeCoordinateMap
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKΩ : K ⊆ G.relativeCoordinateDomain L f qG qL) :
    ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (G.relativeCoordinateMap L qG qL (σ k)) (interior K) := by
  let := (G.limitFlow.metricAt 0).toMetricSpace
  let := (L.limitFlow.metricAt 0).toMetricSpace
  have hKc : K ⊆ (extChartAt (𝓡 n) qG).target := fun _ hx ↦ (hKΩ hx).1
  have hKimage := hK.image_of_continuousOn
    ((contMDiffOn_extChartAt_symm (n := ∞) qG).continuousOn.mono hKc)
  obtain ⟨r₀, hr₀⟩ := hKimage.isBounded.subset_ball G.limitFlow.base
  let r := max r₀ 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKr : MapsTo (extChartAt (𝓡 n) qG).symm K (G.limitFlow.ballAt 0 r) := by
    intro y hy
    change (extChartAt (𝓡 n) qG).symm y ∈
      (G.limitFlow.metricAt 0).ball G.limitFlow.base r
    rw [← (G.limitFlow.metricAt 0).toMetricSpace_ball]
    exact Metric.ball_subset_ball (le_max_left _ _) (hr₀ (mem_image_of_mem _ hy))
  obtain ⟨T, _, _, htarget⟩ := G.exists_compact_relativeCoordinate_target L f hf hconv
    qG qL hK hKΩ
  filter_upwards [hσ.tendsto_atTop.eventually (eventually_relative_map_smooth C F H G L
    hGtime hLtime hGcomplete hLcomplete hsource hr), htarget] with k hk hkt y hy
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) qG).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) qG).mem_nhds (hKc (interior_subset hy)))
  have hl := (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := qL)).contMDiffAt
    (by simpa only [extChartAt_source] using
      (isOpen_extChartAt_source (I := 𝓡 n) qL).mem_nhds (hkt.2 y (interior_subset hy)))
  exact (contMDiffAt_iff_contDiffAt.mp
    (hl.comp y ((hk.2.1 _ (hKr (interior_subset hy))).comp y hc))).contDiffWithinAt

include hGtime hLtime hGcomplete hLcomplete hsource hσ hf hconv in
theorem locally_eventually_smooth_relativeCoordinateMap :
    ∀ y ∈ G.relativeCoordinateDomain L f qG qL,
      ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ y ∈ V ∧
        V ⊆ G.relativeCoordinateDomain L f qG qL ∧
        ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (G.relativeCoordinateMap L qG qL (σ k)) V := by
  intro y hy
  obtain ⟨K, hK, hyK, hKΩ⟩ := exists_compact_between isCompact_singleton
    (G.isOpen_relativeCoordinateDomain L f hf qG qL) (singleton_subset_iff.mpr hy)
  exact ⟨interior K, isOpen_interior, hyK (mem_singleton _), interior_subset.trans hKΩ,
    eventually_contDiffOn_relativeCoordinateMap C F H G L hGtime hLtime hGcomplete hLcomplete
      hsource hσ f hf hconv qG qL hK hKΩ⟩

include hGtime hLtime hGcomplete hLcomplete hsource hmetric hσ hf hconv in
theorem contDiffOn_relativeCoordinateLimit :
    ContDiffOn ℝ ∞
      (fun y ↦ extChartAt (𝓡 n) qL (f ((extChartAt (𝓡 n) qG).symm y)))
      (G.relativeCoordinateDomain L f qG qL) := by
  apply contDiffOn_of_locally_eventually_smooth
    (fun y hy ↦ tendsto_relativeCoordinateMap C F H G L f hconv qG qL hy)
    (locally_eventually_smooth_relativeCoordinateMap C F H G L hGtime hLtime hGcomplete
      hLcomplete hsource hσ f hf hconv qG qL)
  exact locallyEventuallyBoundedDerivatives_relativeCoordinateMap C F H G L hGtime hLtime
    hGcomplete hLcomplete hsource hmetric hσ f hf hconv qG qL

include hGtime hLtime hGcomplete hLcomplete hsource hmetric hσ hf hconv in
theorem tendstoLocallyUniformlyOn_relativeCoordinateJets (m : ℕ) :
    TendstoLocallyUniformlyOn
      (fun k ↦ iteratedFDeriv ℝ m (G.relativeCoordinateMap L qG qL (σ k)))
      (iteratedFDeriv ℝ m
        (fun y ↦ extChartAt (𝓡 n) qL (f ((extChartAt (𝓡 n) qG).symm y))))
      atTop (G.relativeCoordinateDomain L f qG qL) := by
  apply tendstoLocallyUniformlyOn_iteratedFDeriv_of_locally_eventually_smooth
    (fun y hy ↦ tendsto_relativeCoordinateMap C F H G L f hconv qG qL hy)
    (locally_eventually_smooth_relativeCoordinateMap C F H G L hGtime hLtime hGcomplete
      hLcomplete hsource hσ f hf hconv qG qL)
  exact locallyEventuallyBoundedDerivatives_relativeCoordinateMap C F H G L hGtime hLtime
    hGcomplete hLcomplete hsource hmetric hσ f hf hconv qG qL

include hGtime hLtime hGcomplete hLcomplete hsource hmetric hσ hf hconv in
theorem contMDiff_relative_limit : ContMDiff (𝓡 n) (𝓡 n) ∞ f := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨hf.continuousAt, ?_⟩
  have hx : extChartAt (𝓡 n) x x ∈ G.relativeCoordinateDomain L f x (f x) := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change f ((extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)) ∈
      (extChartAt (𝓡 n) (f x)).source
    rw [(extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_source (f x)
  exact ((contDiffOn_relativeCoordinateLimit C F H G L hGtime hLtime hGcomplete hLcomplete
    hsource hmetric hσ f hf hconv x (f x)).contDiffAt
      ((G.isOpen_relativeCoordinateDomain L f hf x (f x)).mem_nhds hx)).contDiffWithinAt

end PoincareConjecture.PointedGeometricConvergence
