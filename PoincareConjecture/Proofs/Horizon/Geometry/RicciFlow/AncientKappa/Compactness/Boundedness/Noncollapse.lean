import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace RicciFlow

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem scalar_monotone_of_terminalHomothety
    {b Q : ℝ} {F : RicciFlow 3 M (Iic b)} {G : RicciFlow 3 M (Iic 0)}
    (hQ : 0 < Q)
    (hcal : ∀ s : ℝ, MetricHomothetyCalculus (F.metric (b + s / Q))
      (G.metric s) (Diffeomorph.refl (𝓡 3) M ∞) Q)
    (hmono : ∀ s t : ℝ, s ≤ t → t ≤ b → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x) :
    ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x,
      (G.connection s).scalarCurvature x ≤ (G.connection t).scalarCurvature x := by
  intro s t hst ht x
  have hs := (hcal s).scalar_eq (F.connection (b + s / Q)) (G.connection s) x
  have ht' := (hcal t).scalar_eq (F.connection (b + t / Q)) (G.connection t) x
  change (G.connection s).scalarCurvature x =
    (F.connection (b + s / Q)).scalarCurvature x / Q at hs
  change (G.connection t).scalarCurvature x =
    (F.connection (b + t / Q)).scalarCurvature x / Q at ht'
  rw [hs, ht']
  apply div_le_div_of_nonneg_right _ hQ.le
  apply hmono (b + s / Q) (b + t / Q) ?_ ?_ x
  · have hdiv := div_le_div_of_nonneg_right hst hQ.le
    linarith
  · have hdiv := div_nonpos_of_nonpos_of_nonneg ht hQ.le
    linarith

variable [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]



theorem metricKappaNoncollapsed_of_ancient_scalar_monotone
    (P : M23NormalizedKappaCompactnessPredecessors)
    (F : RicciFlow 3 M (Iic 0)) {κ : ℝ} (hκ : 0 < κ)
    (hop : ∀ s ≤ 0, ∀ x, (F.connection s).NonnegativeCurvatureOperator x)
    (hnc : AncientKappaNoncollapsed F κ)
    (hmono : ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    {t : ℝ} (ht : t ≤ 0) :
    MetricKappaNoncollapsed (F.metric t) (F.connection t) (κ / 27) := by
  refine ⟨div_pos hκ (by norm_num), ?_⟩
  intro p r hr hbound
  have hr3 : 0 < r / 3 := by positivity
  have hsub : (F.metric t).ball p (r / 3) ⊆ (F.metric t).ball p r := by
    intro q hq
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (by linarith))
  have hvol := hnc (r / 3) hr3 t ht p (r / 3) hr3 le_rfl (by
    intro s hs q hq
    have hpast := ((F.connection s).curvatureTensorNorm_le_scalarCurvature_sharp
      (P.tensor_calculus 3 M (F.metric s) (F.connection s)) q
      (hop s (hs.2.trans ht) q)).trans (hmono s t hs.2 ht q)
    have htrace := (F.connection t).scalarCurvature_le_curvatureTensorNorm_sharp q
    have hterminal := (le_abs_self _).trans (hbound q (hsub hq))
    rw [abs_of_nonneg (show 0 ≤ (F.connection s).curvatureTensorNorm q from
      Real.sqrt_nonneg _)]
    have hscale : (r / 3)⁻¹ ^ 2 = 9 * r⁻¹ ^ 2 := by
      rw [inv_div, div_pow]
      norm_num [div_eq_mul_inv]
    rw [hscale]
    norm_num at htrace
    nlinarith [sq_nonneg r⁻¹])
  have hconstant : κ * (r / 3) ^ 3 = (κ / 27) * r ^ 3 := by ring
  rw [hconstant] at hvol
  exact hvol.trans (MeasureTheory.measure_mono hsub)

end RicciFlow

namespace RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance noncollapseCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)


theorem interiorLimit_metricKappaNoncollapsed
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ k, AncientKappaNoncollapsed (F k) κ)
    (hmono : ∀ k s t, s ≤ t → t ≤ 0 → ∀ x,
      ((F k).connection s).scalarCurvature x ≤ ((F k).connection t).scalarCurvature x)
    (G : AncientPointedGeometricConvergence C
      (fun k t => (F k).metric (t - δ)) p δ)
    (hcomplete : ∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) :
    ∀ t ∈ Iio δ, MetricKappaNoncollapsed
      (G.limitFlow.metric t) (G.limitFlow.connection t) (κ / 27) := by
  let Fseq (k : ℕ) := (F k).bufferedExpandingFlow δ
  have htime (a b : ℝ) (hb : b < δ) :
      ∀ᶠ k : ℕ in atTop, Icc a b ⊆ (fun t : ℝ => t - δ) ⁻¹' Iic 0 :=
    Eventually.of_forall fun k t ht => by
      change t - δ ≤ 0
      linarith [ht.2]
  have hvolume := G.volume_lower_bound_of_static_noncollapse Fseq hδ htime hcomplete
    (κ / 27) (by
      intro t ht
      refine Eventually.of_forall fun k x r hr hcurv => ?_
      have hstatic := (F k).metricKappaNoncollapsed_of_ancient_scalar_monotone P hκ
        (hop k) (hnc k) (hmono k) (show t - δ ≤ 0 by change t < δ at ht; linarith)
      change ENNReal.ofReal ((κ / 27) * r ^ 3) ≤
        ((F k).metric (t - δ)).volumeMeasure (((F k).metric (t - δ)).ball x r)
      simpa only [calibratedMetricVolume_eq_volumeMeasure] using hstatic.2 x r hr hcurv)
  intro t ht
  refine ⟨div_pos hκ (by norm_num), ?_⟩
  intro x r hr hcurv
  rw [calibratedMetricVolume_eq_volumeMeasure]
  exact hvolume t ht x r hr hcurv

end RawAncientSequence
end PoincareConjecture
