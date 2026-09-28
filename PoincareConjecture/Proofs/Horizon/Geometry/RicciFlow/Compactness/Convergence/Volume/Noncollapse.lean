import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.AtPoint
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature.Uniform

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
  (G : PointedGeometricConvergence S)

theorem eventually_source_static_curvature_bound
    {t r ρ : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (p : G.limitCarrier.carrier) (hρ : 0 < ρ) (hρr : ρ < r)
    (hcurv : ∀ x ∈ (G.limitFlow.metricAt t).ball p r,
      |(G.limitFlow.flow.connection t).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ∀ᶠ k in atTop, ∀ x ∈ ((S.flow (G.subsequence k)).metricAt t).ball
      ((G.embedding k).toFun (t, p)).2 ρ,
      |((S.flow (G.subsequence k)).flow.connection t).curvatureTensorNorm x| ≤ ρ⁻¹ ^ 2 := by
  let g := G.limitFlow.metricAt t
  let : EMetricSpace G.limitCarrier.carrier := G.limitCarrier.metricEMetricSpace g
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
  have hrad : r⁻¹ ^ 2 < ρ⁻¹ ^ 2 := by
    have hi := (inv_lt_inv₀ hr hρ).mpr hρr
    nlinarith [inv_pos.mpr hρ, inv_pos.mpr hr]
  have hbounds := G.eventually_curvatureTensorNorm_lt_on_compact
    ((isCompact_singleton (x := t)).prod hA)
    (fun z hz => by rw [mem_singleton_iff.mp hz.1]; exact ht)
    (B := ρ⁻¹ ^ 2) (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      rcases mem_singleton_iff.mp hs with rfl
      exact (le_abs_self _).trans (hcurv x (hAr hx)) |>.trans_lt hrad)
  filter_upwards [hbounds, G.eventually_source_ball_subset_image_ball_at
    ht hcomplete p hρ hC] with k hk hcover x hx
  obtain ⟨y, hy, rfl⟩ := hcover hx
  rw [hCr] at hy
  rw [abs_of_nonneg (show 0 ≤ ((S.flow (G.subsequence k)).flow.connection t).curvatureTensorNorm
    ((G.embedding k).toFun (t, y)).2 from Real.sqrt_nonneg _)]
  exact (hk (t, y) ⟨mem_singleton t, subset_closure hy⟩).le

theorem ball_volume_lower_bound_of_eventually_static_noncollapse
    {t r : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (p : G.limitCarrier.carrier) (hr : 0 < r) (κ : ℝ)
    (hsource : ∀ ρ : ℝ, 0 < ρ → ρ < r → ∀ᶠ k in atTop,
      (∀ x ∈ ((S.flow (G.subsequence k)).metricAt t).ball
        ((G.embedding k).toFun (t, p)).2 ρ,
        |((S.flow (G.subsequence k)).flow.connection t).curvatureTensorNorm x| ≤ ρ⁻¹ ^ 2) →
      ENNReal.ofReal (κ * ρ ^ n) ≤ ((S.flow (G.subsequence k)).metricAt t).volumeMeasure
        (((S.flow (G.subsequence k)).metricAt t).ball ((G.embedding k).toFun (t, p)).2 ρ))
    (hcurv : ∀ x ∈ (G.limitFlow.metricAt t).ball p r,
      |(G.limitFlow.flow.connection t).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (κ * r ^ n) ≤
      (G.limitFlow.metricAt t).volumeMeasure ((G.limitFlow.metricAt t).ball p r) := by
  have hsmall (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
      ENNReal.ofReal (κ * ρ ^ n) ≤
        (G.limitFlow.metricAt t).volumeMeasure ((G.limitFlow.metricAt t).ball p r) := by
    have hevent := (hsource ρ hρ hρr).mp
      ((G.eventually_source_static_curvature_bound ht hcomplete p hρ hρr hcurv).mono
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

end PoincareConjecture.PointedGeometricConvergence
