import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.RescalingGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}
  (G : AncientCompactTimeConvergence S)

theorem eventually_source_curvature_bound_of_limit
    {t r ρ : ℝ} (ht : t < 0) (p : G.limit.carrier.carrier) (hρ : 0 < ρ) (hρr : ρ < r)
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limit.flow.metric t).ball p r,
      |(G.limit.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ∀ᶠ k in atTop, ∀ s ∈ Ioc (t - ρ ^ 2) t,
      ∀ x ∈ ((S.rescaling (G.subsequence k)).flow.metric t).ball
          ((G.embedding k).toFun (t, p)).2 ρ,
        |((S.rescaling (G.subsequence k)).flow.connection s).curvatureTensorNorm x| ≤ ρ⁻¹ ^ 2 := by
  let g := G.limit.flow.metric t
  let : EMetricSpace G.limit.carrier.carrier := G.limit.carrier.metricEMetricSpace g
  obtain ⟨a, hρa, har⟩ := exists_between hρr
  have ha : 0 < a := hρ.trans hρa
  have hr : 0 < r := hρ.trans hρr
  let C := a / ρ
  have hC : 1 < C := (one_lt_div hρ).mpr hρa
  have hCr : C * ρ = a := div_mul_cancel₀ a hρ.ne'
  let A := closure (g.ball p a)
  have hA : IsCompact A := g.isCompact_closure_ball_of_metricComplete (G.limit.complete t ht) p a
  have hAr : A ⊆ g.ball p r := by
    intro x hx
    have hd : edist p x ≤ ENNReal.ofReal a :=
      closure_minimal (fun _ hy ↦ le_of_lt hy)
        (isClosed_le (continuous_const.edist continuous_id) continuous_const) hx
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr har)
  have htρ : t - ρ ^ 2 < 0 := by nlinarith [sq_nonneg ρ]
  have htime : Icc (t - ρ ^ 2) t ⊆ Ioc (t - r ^ 2) t := by
    intro s hs
    exact ⟨by nlinarith [hs.1], hs.2⟩
  have hrad : r⁻¹ ^ 2 < ρ⁻¹ ^ 2 := by
    have hi := (inv_lt_inv₀ hr hρ).mpr hρr
    nlinarith [inv_pos.mpr hρ, inv_pos.mpr hr]
  have hbounds := G.eventually_curvatureTensorNorm_lt_on_compact (isCompact_Icc.prod hA)
    (fun z hz ↦ lt_of_le_of_lt hz.1.2 ht)
    (fun z hz ↦ (le_abs_self _).trans (hcurv z.1 (htime hz.1) z.2 (hAr hz.2)) |>.trans_lt hrad)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hA
  filter_upwards [hbounds, G.eventually_source_ball_subset_image_ball ht p hρ hC,
    eventually_timeWindow_mem_nhds htρ, eventually_timeWindow_mem_nhds ht,
    eventually_ge_atTop j] with k hk hcover hkl hkt hjk s hs x hx
  obtain ⟨y, hy, rfl⟩ := hcover hx
  rw [hCr] at hy
  have hyA : y ∈ A := subset_closure hy
  have hs' : s ∈ Icc (t - ρ ^ 2) t := ⟨hs.1.le, hs.2⟩
  have hsl : s ∈ ancientM18TimeWindow k :=
    ⟨(mem_of_mem_nhds hkl).1.trans hs'.1, hs'.2.trans (mem_of_mem_nhds hkt).2⟩
  change |((S.rescaling (G.subsequence k)).flow.connection s).curvatureTensorNorm
    ((G.embedding k).toFun (t, y)).2| ≤ ρ⁻¹ ^ 2
  rw [← G.spatial_time_independent k s t y hsl (mem_of_mem_nhds hkt)
    (G.exhaustion_monotone hjk (hj hyA))]
  rw [abs_of_nonneg (show 0 ≤ ((S.rescaling (G.subsequence k)).flow.connection s).curvatureTensorNorm
    ((G.embedding k).toFun (s, y)).2 from Real.sqrt_nonneg _)]
  exact (hk (s, y) ⟨hs', hyA⟩).le

theorem noncollapsed_ball_of_curvature_bound
    {t r : ℝ} (ht : t < 0) (p : G.limit.carrier.carrier) (hr : 0 < r)
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limit.flow.metric t).ball p r,
      |(G.limit.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (K.kappa * r ^ n) ≤ calibratedMetricVolume (G.limit.flow.metric t)
      ((G.limit.flow.metric t).ball p r) := by
  have hsmall (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
      ENNReal.ofReal (K.kappa * ρ ^ n) ≤ calibratedMetricVolume (G.limit.flow.metric t)
        ((G.limit.flow.metric t).ball p r) := by
    have hv := ge_of_tendsto (G.tendsto_calibratedMetricVolume_ball ht p hρ)
      ((G.eventually_source_curvature_bound_of_limit ht p hρ hρr hcurv).mono fun k hk ↦
        (S.rescaling (G.subsequence k)).noncollapsed t ht ((G.embedding k).toFun (t, p)).2 ρ hρ hk)
    apply hv.trans (measure_mono ?_)
    exact fun x hx ↦ hx.trans_le (ENNReal.ofReal_le_ofReal hρr.le)
  apply le_of_tendsto (f := fun ρ : ℝ ↦ ENNReal.ofReal (K.kappa * ρ ^ n))
    (x := 𝓝[<] r) ((ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow n))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds] with ρ hρr hρ
  exact hsmall ρ hρ hρr

theorem kappa_noncollapsed : AncientLimitKappaNoncollapsed G.limit K.kappa := by
  intro r₀ _ t ht p r hr _ hcurv
  exact G.noncollapsed_ball_of_curvature_bound ht p hr hcurv

end PoincareConjecture.AncientCompactTimeConvergence
