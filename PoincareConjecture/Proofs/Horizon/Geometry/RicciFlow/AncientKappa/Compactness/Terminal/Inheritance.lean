import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.ParabolicNoncollapse










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalInheritanceConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

private theorem norm_eq_of_metric_eq
    {g h : RiemannianMetric 3 G.limitCarrier.carrier}
    (D : LeviCivitaData g) (E : LeviCivitaData h)
    (heq : g = h) (x : G.limitCarrier.carrier) :
    D.curvatureTensorNorm x = E.curvatureTensorNorm x := by
  subst h
  exact D.horizon_curvatureTensorNorm_eq E x



theorem closedLimit_noncollapsed
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcomplete : ∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t))
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hmetric : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1)) :
    AncientKappaNoncollapsed F κ := by
  have hnorm (t : ℝ) (ht : t < 0) (x : G.limitCarrier.carrier) :
      (F.connection t).curvatureTensorNorm x =
        (G.limitFlow.connection (t + 1)).curvatureTensorNorm x :=
    norm_eq_of_metric_eq S G (F.connection t) (G.limitFlow.connection (t + 1))
      (hmetric t ht) x
  have hinterior (t : ℝ) (ht : t < 0) (p : G.limitCarrier.carrier)
      (r : ℝ) (hr : 0 < r)
      (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
      ENNReal.ofReal (κ * r ^ 3) ≤
        (F.metric t).volumeMeasure ((F.metric t).ball p r) := by
    have h := S.interiorLimit_noncollapsed_ball G hcomplete
      (t := t + 1) (by linarith) p hr (by
        intro s hs x hx
        have hs0 : s - 1 < 0 := by linarith [hs.2]
        have hsI : s - 1 ∈ Ioc (t - r ^ 2) t :=
          ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hb : x ∈ (F.metric t).ball p r := by rwa [hmetric t ht]
        have hn := hnorm (s - 1) hs0 x
        rw [sub_add_cancel] at hn
        rw [← hn]
        exact hcurv (s - 1) hsI x hb)
    rw [← hmetric t ht, calibratedMetricVolume_eq_volumeMeasure] at h
    exact h
  have hoperator := S.closedLimit_nonnegativeCurvatureOperator G P F hmetric
  intro r₀ _ t ht p r hr _ hcurv
  rw [calibratedMetricVolume_eq_volumeMeasure]
  rcases lt_or_eq_of_le ht with ht | rfl
  · exact hinterior t ht p r hr hcurv
  · exact F.terminal_ball_volume_lower_bound_of_interior_noncollapse κ
      (fun s hs x v => ((F.connection s).ricci_bounds_of_nonnegative_curvatureOperator
        (P.tensor_calculus 3 G.limitCarrier.carrier (F.metric s) (F.connection s))
        x (hoperator s hs x) v).1) hinterior p hr
      (by simpa only [zero_sub] using hcurv)

end PoincareConjecture.NormalizedKappaSolutionSequence
