import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry








set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal
universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J K : Set ℝ}
  (F : RicciFlow n M J) (c : ℝ) (hc : 0 < c) (τ : ℝ)
  (hKJ : Set.MapsTo (fun s : ℝ ↦ τ + s / c) K J)
  (hK : K.OrdConnected) (hne : K.Nontrivial)

theorem parabolicRescale_ricci (s : ℝ) (x : M) (u v : TangentSpace (𝓡 n) x) :
    ((F.parabolicRescale c hc τ hKJ hK hne).connection s).ricci x u v =
      (F.connection (τ + s / c)).ricci x u v :=
  rescaledMetric_ricci _ _ c hc x u v

theorem parabolicRescale_scalarCurvature (s : ℝ) (x : M) :
    ((F.parabolicRescale c hc τ hKJ hK hne).connection s).scalarCurvature x =
      c⁻¹ * (F.connection (τ + s / c)).scalarCurvature x :=
  rescaledMetric_scalarCurvature _ _ c hc x

theorem parabolicRescale_nonnegativeCurvatureOperator (s : ℝ) (x : M)
    (h : (F.connection (τ + s / c)).NonnegativeCurvatureOperator x) :
    ((F.parabolicRescale c hc τ hKJ hK hne).connection s).NonnegativeCurvatureOperator x :=
  rescaledMetric_nonnegativeCurvatureOperator _ _ c hc x h

theorem parabolicRescale_metricComplete [T3Space M] (s : ℝ)
    (h : MetricComplete (F.metric (τ + s / c))) :
    MetricComplete ((F.parabolicRescale c hc τ hKJ hK hne).metric s) :=
  metricComplete_rescaledMetric _ c hc h

theorem parabolicRescale_edist (s : ℝ) (x y : M) :
    ((F.parabolicRescale c hc τ hKJ hK hne).metric s).edist x y =
      ENNReal.ofReal (Real.sqrt c) * (F.metric (τ + s / c)).edist x y :=
  rescaledMetric_edist _ c hc x y

theorem parabolicRescale_pathELength (s : ℝ) (γ : ℝ → M) (a b : ℝ) :
    ((F.parabolicRescale c hc τ hKJ hK hne).metric s).pathELength γ a b =
      ENNReal.ofReal (Real.sqrt c) * (F.metric (τ + s / c)).pathELength γ a b :=
  rescaledMetric_pathELength _ c hc γ a b

theorem parabolicRescale_volumeMeasure [T3Space M] [MeasurableSpace M] [BorelSpace M]
    (s : ℝ) :
    ((F.parabolicRescale c hc τ hKJ hK hne).metric s).volumeMeasure =
      (ENNReal.ofReal (Real.sqrt c) ^ n) • (F.metric (τ + s / c)).volumeMeasure :=
  rescaledMetric_volumeMeasure _ c hc

theorem parabolicRescale_ball (s : ℝ) (x : M) (r : ℝ) :
    ((F.parabolicRescale c hc τ hKJ hK hne).metric s).ball x r =
      (F.metric (τ + s / c)).ball x (r / Real.sqrt c) :=
  rescaledMetric_ball_allDimensions _ c hc x r

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.RicciFlow



theorem exists_parabolicRescaling
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J K : Set ℝ}
    (F : RicciFlow n M J) (c : ℝ) (hc : 0 < c) (τ : ℝ)
    (hKJ : Set.MapsTo (fun s : ℝ ↦ τ + s / c) K J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) :
    ∃ G : RicciFlow n M K,
      (∀ s, G.metric s = rescaledMetric (F.metric (τ + s / c)) c hc) ∧
      (∀ s x u v, (G.connection s).ricci x u v =
        (F.connection (τ + s / c)).ricci x u v) ∧
      (∀ s x, (G.connection s).scalarCurvature x =
        c⁻¹ * (F.connection (τ + s / c)).scalarCurvature x) ∧
      (∀ s, MetricComplete (F.metric (τ + s / c)) → MetricComplete (G.metric s)) ∧
      (∀ s x, (F.connection (τ + s / c)).NonnegativeCurvatureOperator x →
        (G.connection s).NonnegativeCurvatureOperator x) ∧
      (∀ s x y, (G.metric s).edist x y =
        ENNReal.ofReal (Real.sqrt c) * (F.metric (τ + s / c)).edist x y) ∧
      (∀ s, (G.metric s).volumeMeasure =
        (ENNReal.ofReal (Real.sqrt c) ^ n) • (F.metric (τ + s / c)).volumeMeasure) := by
  exact ⟨F.parabolicRescale c hc τ hKJ hK hne,
    F.parabolicRescale_metric c hc τ hKJ hK hne,
    F.parabolicRescale_ricci c hc τ hKJ hK hne,
    F.parabolicRescale_scalarCurvature c hc τ hKJ hK hne,
    F.parabolicRescale_metricComplete c hc τ hKJ hK hne,
    F.parabolicRescale_nonnegativeCurvatureOperator c hc τ hKJ hK hne,
    F.parabolicRescale_edist c hc τ hKJ hK hne,
    F.parabolicRescale_volumeMeasure c hc τ hKJ hK hne⟩

end PoincareConjecture.RicciFlow
