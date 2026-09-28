import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace AncientKappaSolution

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem metricKappaNoncollapsed_of_m23_predecessors
    (K : AncientKappaSolution 3 M) (P : M23NormalizedKappaCompactnessPredecessors)
    {t : ℝ} (ht : t ≤ 0) :
    MetricKappaNoncollapsed (K.flow.metric t) (K.flow.connection t) (K.kappa / 27) := by
  refine ⟨div_pos K.kappa_pos (by norm_num), ?_⟩
  intro p r hr hbound
  have hr3 : 0 < r / 3 := by positivity
  have hsub : (K.flow.metric t).ball p (r / 3) ⊆ (K.flow.metric t).ball p r := by
    intro q hq
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (by linarith))
  have hvol := K.noncollapsed (r / 3) hr3 t ht p (r / 3) hr3 le_rfl (by
    intro s hs q hq
    have hpast := P.past_norm_le_scalar M K s t hs.2 ht q
    have htrace := (K.flow.connection t).scalarCurvature_le_curvatureTensorNorm_sharp q
    have hterminal := (le_abs_self _).trans (hbound q (hsub hq))
    rw [abs_of_nonneg (show 0 ≤ (K.flow.connection s).curvatureTensorNorm q from
      Real.sqrt_nonneg _)]
    have hscale : (r / 3)⁻¹ ^ 2 = 9 * r⁻¹ ^ 2 := by
      rw [inv_div, div_pow]
      norm_num [div_eq_mul_inv]
    rw [hscale]
    norm_num at htrace
    nlinarith [sq_nonneg r⁻¹])
  have hconstant : K.kappa * (r / 3) ^ 3 = (K.kappa / 27) * r ^ 3 := by ring
  rw [hconstant] at hvol
  exact hvol.trans (MeasureTheory.measure_mono hsub)

end AncientKappaSolution

namespace NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance flowCarrierConnected (C : FlowCarrier 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)



theorem interiorLimit_metricKappaNoncollapsed
    (P : M23NormalizedKappaCompactnessPredecessors)
    (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
      (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)
    (hcomplete : ∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t)) :
    ∀ t : ℝ, t < 1 → MetricKappaNoncollapsed
      (G.limitFlow.metric t) (G.limitFlow.connection t) (kappa / 27) := by
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  have htime (a b : ℝ) (hb : b < 1) :
      ∀ᶠ k : ℕ in atTop, Icc a b ⊆ (fun t : ℝ => t - 1) ⁻¹' Iic 0 :=
    Eventually.of_forall fun k t ht => by
      change t - 1 ≤ 0
      linarith [ht.2]
  have hvolume := G.volume_lower_bound_of_static_noncollapse F
    (by norm_num) htime hcomplete (kappa / 27) (by
      intro t ht
      refine Eventually.of_forall fun k x r hr hcurv => ?_
      have hnc := (S.term k).flow.metricKappaNoncollapsed_of_m23_predecessors P
        (show t - 1 ≤ 0 by change t < 1 at ht; linarith)
      rw [(S.term k).kappa_eq] at hnc
      change ENNReal.ofReal ((kappa / 27) * r ^ 3) ≤
        ((S.term k).flow.flow.metric (t - 1)).volumeMeasure
          (((S.term k).flow.flow.metric (t - 1)).ball x r)
      simpa only [calibratedMetricVolume_eq_volumeMeasure] using hnc.2 x r hr hcurv)
  intro t ht
  refine ⟨div_pos S.kappa_pos (by norm_num), ?_⟩
  intro x r hr hcurv
  rw [calibratedMetricVolume_eq_volumeMeasure]
  exact hvolume t ht x r hr hcurv

end NormalizedKappaSolutionSequence
end PoincareConjecture
