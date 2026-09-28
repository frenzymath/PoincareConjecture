import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.AtPoint
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.TimeIndependent
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

namespace PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
  (G : PointedGeometricConvergence S)



theorem eventually_source_parabolic_curvature_bound
    {t r ρ : ℝ} (htime : Icc (t - r ^ 2) t ⊆ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (p : G.limitCarrier.carrier) (hρ : 0 < ρ) (hρr : ρ < r)
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limitFlow.metricAt t).ball p r,
      |(G.limitFlow.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ∀ᶠ k in atTop, ∀ s ∈ Ioc (t - ρ ^ 2) t,
      ∀ x ∈ ((S.flow (G.subsequence k)).metricAt t).ball
        ((G.embedding k).toFun (t, p)).2 ρ,
        |((S.flow (G.subsequence k)).flow.connection s).curvatureTensorNorm x| ≤ ρ⁻¹ ^ 2 := by
  let g := G.limitFlow.metricAt t
  let : EMetricSpace G.limitCarrier.carrier := G.limitCarrier.metricEMetricSpace g
  have ht : t ∈ Ioo T' T := htime ⟨by nlinarith [sq_nonneg r], le_rfl⟩
  obtain ⟨a, hρa, har⟩ := exists_between hρr
  have hr : 0 < r := hρ.trans hρr
  let C := a / ρ
  have hC : 1 < C := (one_lt_div hρ).mpr hρa
  have hCr : C * ρ = a := div_mul_cancel₀ a hρ.ne'
  let A := closure (g.ball p a)
  have hA : IsCompact A := g.isCompact_closure_ball_of_metricComplete hcomplete p a
  have hAr : A ⊆ g.ball p r := by
    intro x hx
    have hd : edist p x ≤ ENNReal.ofReal a :=
      closure_minimal (fun _ hy => le_of_lt hy)
        (isClosed_le (continuous_const.edist continuous_id) continuous_const) hx
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr har)
  have htimes : Icc (t - ρ ^ 2) t ⊆ Ioc (t - r ^ 2) t := by
    intro s hs
    exact ⟨by nlinarith [hs.1], hs.2⟩
  have hrad : r⁻¹ ^ 2 < ρ⁻¹ ^ 2 := by
    have hi := (inv_lt_inv₀ hr hρ).mpr hρr
    nlinarith [inv_pos.mpr hρ, inv_pos.mpr hr]
  have hbounds := G.eventually_curvatureTensorNorm_lt_on_compact (isCompact_Icc.prod hA)
    (fun z hz => htime ⟨(htimes hz.1).1.le, (htimes hz.1).2⟩)
    (fun z hz => (le_abs_self _).trans
      (hcurv z.1 (htimes hz.1) z.2 (hAr hz.2)) |>.trans_lt hrad)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hA
  filter_upwards [hbounds, G.eventually_source_ball_subset_image_ball_at
    ht hcomplete p hρ hC, eventually_ge_atTop j] with k hk hcover hjk s hs x hx
  obtain ⟨y, hy, rfl⟩ := hcover hx
  rw [hCr] at hy
  have hyA : y ∈ A := subset_closure hy
  have hs' : s ∈ Icc (t - ρ ^ 2) t := ⟨hs.1.le, hs.2⟩
  have hsI : s ∈ Ioo T' T := htime ⟨(htimes hs').1.le, hs.2⟩
  change |((S.flow (G.subsequence k)).flow.connection s).curvatureTensorNorm
    ((G.embedding k).toFun (t, y)).2| ≤ ρ⁻¹ ^ 2
  rw [← (G.embedding k).spatial_eq_of_mem hsI ht
    (G.exhaustion_monotone hjk (hj hyA))]
  rw [abs_of_nonneg (show 0 ≤ ((S.flow (G.subsequence k)).flow.connection s).curvatureTensorNorm
    ((G.embedding k).toFun (s, y)).2 from Real.sqrt_nonneg _)]
  exact (hk (s, y) ⟨hs', hyA⟩).le



theorem ball_volume_lower_bound_of_eventually_parabolic_noncollapse
    {t r : ℝ} (htime : Icc (t - r ^ 2) t ⊆ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (p : G.limitCarrier.carrier) (hr : 0 < r) (κ : ℝ)
    (hsource : ∀ ρ : ℝ, 0 < ρ → ρ < r → ∀ᶠ k in atTop,
      (∀ s ∈ Ioc (t - ρ ^ 2) t,
        ∀ x ∈ ((S.flow (G.subsequence k)).metricAt t).ball
          ((G.embedding k).toFun (t, p)).2 ρ,
          |((S.flow (G.subsequence k)).flow.connection s).curvatureTensorNorm x| ≤ ρ⁻¹ ^ 2) →
      ENNReal.ofReal (κ * ρ ^ n) ≤ ((S.flow (G.subsequence k)).metricAt t).volumeMeasure
        (((S.flow (G.subsequence k)).metricAt t).ball ((G.embedding k).toFun (t, p)).2 ρ))
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limitFlow.metricAt t).ball p r,
      |(G.limitFlow.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (κ * r ^ n) ≤
      (G.limitFlow.metricAt t).volumeMeasure ((G.limitFlow.metricAt t).ball p r) := by
  have ht : t ∈ Ioo T' T := htime ⟨by nlinarith [sq_nonneg r], le_rfl⟩
  have hsmall (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
      ENNReal.ofReal (κ * ρ ^ n) ≤
        (G.limitFlow.metricAt t).volumeMeasure ((G.limitFlow.metricAt t).ball p r) := by
    have hevent := (hsource ρ hρ hρr).mp
      ((G.eventually_source_parabolic_curvature_bound htime hcomplete p hρ hρr hcurv).mono
        fun _ hk hnoncollapse => hnoncollapse hk)
    have hv := ge_of_tendsto (G.tendsto_volumeMeasure_ball_at ht hcomplete p hρ) hevent
    exact hv.trans (measure_mono (fun _ hx =>
      hx.trans_le (ENNReal.ofReal_le_ofReal hρr.le)))
  apply le_of_tendsto (f := fun ρ : ℝ => ENNReal.ofReal (κ * ρ ^ n))
    (x := 𝓝[<] r)
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow n))).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds] with ρ hρr hρ
  exact hsmall ρ hρ hρr

end PointedGeometricConvergence

namespace NormalizedKappaSolutionSequence

local instance parabolicFlowCarrierConnected (C : FlowCarrier 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)



theorem interiorLimit_noncollapsed_ball
    (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
      (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)
    (hcomplete : ∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t))
    {t r : ℝ} (ht : t < 1) (p : G.limitCarrier.carrier) (hr : 0 < r)
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limitFlow.metric t).ball p r,
      |(G.limitFlow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (kappa * r ^ 3) ≤ calibratedMetricVolume (G.limitFlow.metric t)
      ((G.limitFlow.metric t).ball p r) := by
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
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
    hwindow (hcomplete t ht) p hr kappa ?_ hcurv
  intro ρ hρ _
  refine Eventually.of_forall fun k hk => ?_
  let B := S.term (G.subsequence (k + 0))
  have hnc := B.flow.noncollapsed ρ hρ (t - 1) (by linarith)
    (G.embedding (k + 0) p) ρ hρ le_rfl (by
      intro s hs x hx
      have hs' : s + 1 ∈ Ioc (t - ρ ^ 2) t := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hbound := hk (s + 1) hs' x hx
      change |(B.flow.flow.connection (s + 1 - 1)).curvatureTensorNorm x| ≤ ρ⁻¹ ^ 2 at hbound
      have hshift : s + 1 - 1 = s := by ring
      rw [hshift] at hbound
      exact hbound)
  rw [B.kappa_eq, calibratedMetricVolume_eq_volumeMeasure] at hnc
  exact hnc

end NormalizedKappaSolutionSequence

end PoincareConjecture
