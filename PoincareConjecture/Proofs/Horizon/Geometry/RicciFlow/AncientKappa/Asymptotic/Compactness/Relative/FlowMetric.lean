import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.MetricLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Diffeomorphism








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_extChartAt_center
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (x : M) (v w : TangentSpace (𝓡 n) x) :
    g.pullbackCoefficients (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x) v w =
      g.inner x v w := by
  have hd : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x) =
      ContinuousLinearMap.id ℝ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  change g.inner ((extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x) v)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x) w) = _
  erw [hd, (extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)]
  rfl

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

theorem relative_limit_metric_inner_eq
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
    (t : ℝ) (hGt : t ∈ Ioo a b) (hLt : t ∈ Ioo c d)
    (hmetrict : ∀ k, (F (G.subsequence k)).metricAt t = (H (L.subsequence k)).metricAt t)
    (x : G.limitCarrier.carrier) (v w : TangentSpace (𝓡 n) x) :
    (L.limitFlow.metricAt t).inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (mfderiv (𝓡 n) (𝓡 n) f x w) = (G.limitFlow.metricAt t).inner x v w := by
  let fc := fun y ↦ extChartAt (𝓡 n) (f x) (f ((extChartAt (𝓡 n) x).symm y))
  have hx : extChartAt (𝓡 n) x x ∈ G.relativeCoordinateDomain L f x (f x) := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change f ((extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)) ∈
      (extChartAt (𝓡 n) (f x)).source
    rw [(extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_source (f x)
  have hcoeff := relativeCoordinateLimit_pullback_at_time C F H G L hGtime hLtime hGcomplete
    hLcomplete hsource hmetric hσ f hf hconv x (f x) t hGt hLt hmetrict _ hx v w
  have hfc : fc (extChartAt (𝓡 n) x x) = extChartAt (𝓡 n) (f x) (f x) := by
    dsimp only [fc]
    rw [(extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)]
  have hfd : mfderiv (𝓡 n) (𝓡 n) f x = fderiv ℝ fc (extChartAt (𝓡 n) x x) := by
    have hs := (contMDiff_relative_limit C F H G L hGtime hLtime hGcomplete hLcomplete
      hsource hmetric hσ f hf hconv x).mdifferentiableAt (by simp)
    simp only [mfderiv, hs, if_true, ModelWithCorners.range_eq_univ, fderivWithin_univ]
    rfl
  change (L.limitFlow.metricAt t).pullbackCoefficients (extChartAt (𝓡 n) (f x)).symm
      (fc (extChartAt (𝓡 n) x x)) (fderiv ℝ fc (extChartAt (𝓡 n) x x) v)
      (fderiv ℝ fc (extChartAt (𝓡 n) x x) w) =
    (G.limitFlow.metricAt t).pullbackCoefficients (extChartAt (𝓡 n) x).symm
      (extChartAt (𝓡 n) x x) v w at hcoeff
  rw [hfc, RiemannianMetric.pullbackCoefficients_extChartAt_center,
    RiemannianMetric.pullbackCoefficients_extChartAt_center] at hcoeff
  rw [hfd]
  exact hcoeff

end PoincareConjecture.PointedGeometricConvergence
