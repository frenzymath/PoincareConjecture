import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.ParabolicNoncollapse










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientKappaSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance noncollapseCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (K : ∀ k, AncientKappaSolution 3 (C k).carrier) (p : ∀ k, (C k).carrier)



theorem interiorLimit_noncollapsed_ball
    (G : AncientPointedGeometricConvergence C (fun k t => (K k).flow.metric (t - 1)) p 1)
    {κ : ℝ} (hkappa : ∀ k, (K k).kappa = κ)
    (hcomplete : ∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t))
    {t r : ℝ} (ht : t < 1) (q : G.limitCarrier.carrier) (hr : 0 < r)
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limitFlow.metric t).ball q r,
      |(G.limitFlow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (κ * r ^ 3) ≤ calibratedMetricVolume (G.limitFlow.metric t)
      ((G.limitFlow.metric t).ball q r) := by
  let F (k : ℕ) : RicciFlow 3 (C k).carrier ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (K k).flow.bufferedExpandingFlow 1
  obtain ⟨a, b, ha, hb, hb1, hwindow⟩ := exists_ancient_window_of_isCompact
    (by norm_num : (0 : ℝ) < 1) isCompact_Icc
    (show Icc (t - r ^ 2) t ⊆ Iio 1 from fun s hs => hs.2.trans_lt ht)
  have hsub : ∀ k : ℕ, Ioo a b ⊆ (fun u : ℝ => u - 1) ⁻¹' Iic 0 := by
    intro k u hu
    change u - 1 ≤ 0
    linarith [hu.2]
  let W := G.window F (ha.trans hb) hb1.le 0 hsub
  rw [calibratedMetricVolume_eq_volumeMeasure]
  apply W.ball_volume_lower_bound_of_eventually_parabolic_noncollapse
    hwindow (hcomplete t ht) q hr κ ?_ hcurv
  intro ρ hρ _
  refine Eventually.of_forall fun k hk => ?_
  have hnc := (K (G.subsequence (k + 0))).noncollapsed ρ hρ (t - 1) (by linarith)
    (G.embedding (k + 0) q) ρ hρ le_rfl (by
      intro s hs x hx
      have hs' : s + 1 ∈ Ioc (t - ρ ^ 2) t := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hbound := hk (s + 1) hs' x hx
      change |((K (G.subsequence (k + 0))).flow.connection (s + 1 - 1)).curvatureTensorNorm x|
        ≤ ρ⁻¹ ^ 2 at hbound
      have hshift : s + 1 - 1 = s := by ring
      rw [hshift] at hbound
      exact hbound)
  rw [hkappa, calibratedMetricVolume_eq_volumeMeasure] at hnc
  exact hnc

end PoincareConjecture.AncientKappaSequence
