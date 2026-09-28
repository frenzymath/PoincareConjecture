import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.TimePullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.BilinearConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.TransitionLimit

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
    (t : ℝ) (hGt : t ∈ Ioo a b) (hLt : t ∈ Ioo c d)
    (hmetrict : ∀ k, (F (G.subsequence k)).metricAt t = (H (L.subsequence k)).metricAt t)

include hGtime hLtime hGcomplete hLcomplete hsource hσ hf hconv hGt hLt hmetrict in
theorem eventually_relativeCoordinateMap_pullback_at_time
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ G.relativeCoordinateDomain L f qG qL) :
    ∀ᶠ k in atTop, ∀ v w,
      L.pulledChartCoefficients qL (σ k) t (G.relativeCoordinateMap L qG qL (σ k) y)
        (fderiv ℝ (G.relativeCoordinateMap L qG qL (σ k)) y v)
        (fderiv ℝ (G.relativeCoordinateMap L qG qL (σ k)) y w) =
      G.pulledChartCoefficients qG (σ k) t y v w := by
  let := (G.limitFlow.metricAt 0).toMetricSpace
  let := (L.limitFlow.metricAt 0).toMetricSpace
  obtain ⟨K, hK, hyK, hKΩ⟩ := exists_compact_between isCompact_singleton
    (G.isOpen_relativeCoordinateDomain L f hf qG qL) (singleton_subset_iff.mpr hy)
  have hKc : K ⊆ (extChartAt (𝓡 n) qG).target := fun _ hx ↦ (hKΩ hx).1
  have hKimage := hK.image_of_continuousOn
    ((contMDiffOn_extChartAt_symm (n := ∞) qG).continuousOn.mono hKc)
  obtain ⟨r₀, hr₀⟩ := hKimage.isBounded.subset_ball G.limitFlow.base
  let r := max r₀ 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKr : MapsTo (extChartAt (𝓡 n) qG).symm K (G.limitFlow.ballAt 0 r) := by
    intro z hz
    change (extChartAt (𝓡 n) qG).symm z ∈
      (G.limitFlow.metricAt 0).ball G.limitFlow.base r
    rw [← (G.limitFlow.metricAt 0).toMetricSpace_ball]
    exact Metric.ball_subset_ball (le_max_left _ _) (hr₀ (mem_image_of_mem _ hz))
  obtain ⟨i, hi⟩ := G.exists_exhaustion_superset hKimage
  obtain ⟨j, hj⟩ := L.exists_exhaustion_superset
    ((L.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hLcomplete
      L.limitFlow.base (4 * r))
  obtain ⟨T, _, _, htarget⟩ := G.exists_compact_relativeCoordinate_target L f hf hconv
    qG qL hK hKΩ
  filter_upwards [hσ.tendsto_atTop.eventually (eventually_relative_map_smooth C F H G L
      hGtime hLtime hGcomplete hLcomplete hsource hr),
    hσ.tendsto_atTop.eventually (eventually_ge_atTop i),
    hσ.tendsto_atTop.eventually (eventually_ge_atTop j), htarget,
    eventually_contDiffOn_relativeCoordinateMap C F H G L hGtime hLtime hGcomplete hLcomplete
      hsource hσ f hf hconv qG qL hK hKΩ] with k hk hik hjk hkt hks v w
  apply G.relativeCoordinateMap_pullback_at_time L qG qL (σ k) hGtime hLtime t hGt hLt
    (hmetrict _) isOpen_interior hks ?_ y (hyK (mem_singleton _)) v w
  intro z hz
  have hzr := hKr (interior_subset hz)
  exact ⟨G.exhaustion_monotone hik (hi (mem_image_of_mem _ (interior_subset hz))),
    L.exhaustion_monotone hjk (hj (subset_closure (hk.1 hzr))),
    hkt.2 z (interior_subset hz), hk.2.2 _ hzr⟩

include hGtime hLtime hGcomplete hLcomplete hsource hmetric hσ hf hconv hGt hLt hmetrict in
theorem relativeCoordinateLimit_pullback_at_time :
    let fc := fun y ↦ extChartAt (𝓡 n) qL (f ((extChartAt (𝓡 n) qG).symm y))
    ∀ y ∈ G.relativeCoordinateDomain L f qG qL, ∀ v w,
      (L.limitFlow.metricAt t).pullbackCoefficients (extChartAt (𝓡 n) qL).symm (fc y)
        (fderiv ℝ fc y v) (fderiv ℝ fc y w) =
      (G.limitFlow.metricAt t).pullbackCoefficients (extChartAt (𝓡 n) qG).symm y v w := by
  have hB : TendstoLocallyUniformlyOn (fun k ↦ L.pulledChartCoefficients qL (σ k) t)
      ((L.limitFlow.metricAt t).pullbackCoefficients (extChartAt (𝓡 n) qL).symm)
      atTop (extChartAt (𝓡 n) qL).target := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
      (isOpen_extChartAt_target (I := 𝓡 n) qL)).mpr
    intro K hKc hK
    exact (L.tendstoUniformlyOn_pulledChartCoefficients qL t hLt hK hKc).seq_tendstoUniformlyOn
      σ hσ.tendsto_atTop
  apply CoordinateTransition.pullback_eq_of_tendsto
    (isOpen_extChartAt_target (I := 𝓡 n) qL)
    (Aseq := fun k ↦ G.pulledChartCoefficients qG (σ k) t)
    (Bseq := fun k ↦ L.pulledChartCoefficients qL (σ k) t)
    (fseq := fun k ↦ G.relativeCoordinateMap L qG qL (σ k)) ?_ hB
    ((L.limitFlow.metricAt t).contDiffOn_chartCoefficients qL).continuousOn ?_ ?_ ?_ ?_
  · intro y hy v w
    have hA := (G.tendstoLocallyUniformlyOn_pulledChartCoefficients qG t hGt).tendsto_at hy.1
    exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp
        (hA.comp hσ.tendsto_atTop))
  · intro y hy
    exact (extChartAt (𝓡 n) qL).map_source hy.2
  · intro y hy
    exact tendsto_relativeCoordinateMap C F H G L f hconv qG qL hy
  · intro y hy v
    have hjet := (tendstoLocallyUniformlyOn_relativeCoordinateJets C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hmetric hσ f hf hconv qG qL 1).tendsto_at hy
    have hev := ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin n)) (fun _ : Fin 1 ↦ v)
    simpa only [Function.comp_def, iteratedFDeriv_one_apply] using
      (hev.continuous.tendsto _).comp hjet
  · intro y hy
    exact eventually_relativeCoordinateMap_pullback_at_time C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hσ f hf hconv qG qL t hGt hLt hmetrict hy

end PoincareConjecture.PointedGeometricConvergence
