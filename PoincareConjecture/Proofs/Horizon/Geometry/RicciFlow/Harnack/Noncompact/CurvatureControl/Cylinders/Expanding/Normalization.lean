import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.VolumeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.RescaledSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

theorem rescaledTerminalFlow_ball_volume_lower_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (Q : ℝ) (hQ : 0 < Q) (τ : ℝ) (p : M)
    (r ν : ℝ)
    (hvolume : ENNReal.ofReal (ν * (r / Real.sqrt Q) ^ n) ≤
      (F.metric τ).volumeMeasure ((F.metric τ).ball p (r / Real.sqrt Q))) :
    ENNReal.ofReal (ν * r ^ n) ≤ ((F.rescaledTerminalFlow Q hQ τ).metric 0).volumeMeasure
      (((F.rescaledTerminalFlow Q hQ τ).metric 0).ball p r) := by
  change ENNReal.ofReal (ν * r ^ n) ≤
    (rescaledMetric (F.metric (τ + 0 / Q)) Q hQ).volumeMeasure
      ((rescaledMetric (F.metric (τ + 0 / Q)) Q hQ).ball p r)
  rw [rescaledMetric_volumeMeasure, rescaledMetric_ball_allDimensions, zero_div, add_zero]
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (Real.sqrt Q) ^ n)) hvolume
  have hid : ENNReal.ofReal (Real.sqrt Q) ^ n *
      ENNReal.ofReal (ν * (r / Real.sqrt Q) ^ n) = ENNReal.ofReal (ν * r ^ n) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg Q),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) n)]
    congr 1
    have hne := (Real.sqrt_pos.mpr hQ).ne'
    calc
      Real.sqrt Q ^ n * (ν * (r / Real.sqrt Q) ^ n) =
          ν * (Real.sqrt Q * (r / Real.sqrt Q)) ^ n := by rw [mul_pow]; ring
      _ = ν * r ^ n := by rw [mul_div_cancel₀ _ hne]
  rwa [hid] at h

theorem exists_nonflat_ancient_limit_of_small_rescaled_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (Q τ A L : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k) (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (τ k + (-A k) / Q k) (τ k) ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      ∀ x : (C k).carrier, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      ∀ x ∈ ((F k).metric (τ k)).ball (p k) (L k / Real.sqrt (Q k)),
        ((F k).connection t).scalarCurvature x ≤ 4 * Q k)
    (hnormalize : ∀ k, ((F k).connection (τ k)).scalarCurvature (p k) = Q k)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal (ν * (1 / Real.sqrt (Q k)) ^ (m + 1)) ≤
      ((F k).metric (τ k)).volumeMeasure
        (((F k).metric (τ k)).ball (p k) (1 / Real.sqrt (Q k)))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
        (fun k t => ((F k).rescaledTerminalFlow (Q k) (hQ k) (τ k)).shrink.metric (t - δ))
        (fun k => equivShrink (C k).carrier (p k)) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) := by
  have htime (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-A k) 0) :
      τ k + s / Q k ∈ Icc (τ k + (-A k) / Q k) (τ k) := by
    constructor
    · exact _root_.add_le_add le_rfl (div_le_div_of_nonneg_right hs.1 (hQ k).le)
    · simpa using _root_.add_le_add (le_refl (τ k))
        (div_le_div_of_nonneg_right hs.2 (hQ k).le)
  apply exists_nonflat_ancient_limit_of_small_expanding_cylinders (ν := ν) hC hm C
    (fun k => (fun s : ℝ => τ k + s / Q k) ⁻¹' J k)
    (fun k => (F k).rescaledTerminalFlow (Q k) (hQ k) (τ k)) p A L hA hL
    (fun k => (F k).rescaledTerminalFlow_interior (hQ k) (hJ k))
    (fun k s hs => metricComplete_rescaledMetric _ (Q k) (hQ k)
      (hcomplete k _ (htime k s hs)))
    (fun k s hs x => rescaledMetric_nonnegativeCurvatureOperator _ _ (Q k) (hQ k) x
      (hoperator k _ (htime k s hs) x))
    (fun k => (F k).rescaledTerminalFlow_scalar_le_four
      (Q k) (hQ k) (τ k) (-A k) (L k) (p k) (hscalar k))
    (fun k => (F k).rescaledTerminalFlow_scalar_zero
      (Q k) (hQ k) (τ k) (p k) (hnormalize k)) hν
  filter_upwards [hvolume] with k hk
  exact (F k).rescaledTerminalFlow_unit_volume_lower_bound (Q k) (hQ k) (τ k) (p k) hk

theorem small_rescaled_ancient_limit_ball_volume_lower_bound
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (Q τ A L : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k) (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (τ k + (-A k) / Q k) (τ k) ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      ∀ x : (C k).carrier, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (τ k + (-A k) / Q k) (τ k),
      ∀ x ∈ ((F k).metric (τ k)).ball (p k) (L k / Real.sqrt (Q k)),
        ((F k).connection t).scalarCurvature x ≤ 4 * Q k)
    {ν δ : ℝ} (hν : 0 ≤ ν) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (ν * (r / Real.sqrt (Q k)) ^ (m + 1)) ≤
        ((F k).metric (τ k)).volumeMeasure
          (((F k).metric (τ k)).ball (p k) (r / Real.sqrt (Q k))))
    (G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
      (fun k t => ((F k).rescaledTerminalFlow (Q k) (hQ k) (τ k)).shrink.metric (t - δ))
      (fun k => equivShrink (C k).carrier (p k)) δ)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    ∀ r : ℝ, 0 < r → ENNReal.ofReal ((ν / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
      (G.limitFlow.metric 0).volumeMeasure ((G.limitFlow.metric 0).ball G.base r) := by
  have htime (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-A k) 0) :
      τ k + s / Q k ∈ Icc (τ k + (-A k) / Q k) (τ k) := by
    constructor
    · exact _root_.add_le_add le_rfl (div_le_div_of_nonneg_right hs.1 (hQ k).le)
    · simpa using _root_.add_le_add (le_refl (τ k))
        (div_le_div_of_nonneg_right hs.2 (hQ k).le)
  apply small_ancient_limit_ball_volume_lower_bound hC hm C
    (fun k => (fun s : ℝ => τ k + s / Q k) ⁻¹' J k)
    (fun k => (F k).rescaledTerminalFlow (Q k) (hQ k) (τ k)) p A L hA hL
    (fun k => (F k).rescaledTerminalFlow_interior (hQ k) (hJ k))
    (fun k s hs => metricComplete_rescaledMetric _ (Q k) (hQ k)
      (hcomplete k _ (htime k s hs)))
    (fun k s hs x => rescaledMetric_nonnegativeCurvatureOperator _ _ (Q k) (hQ k) x
      (hoperator k _ (htime k s hs) x))
    (fun k => (F k).rescaledTerminalFlow_scalar_le_four
      (Q k) (hQ k) (τ k) (-A k) (L k) (p k) (hscalar k)) hν hδ hδone _ G hGcomplete
  intro r hr
  filter_upwards [hvolume r hr] with k hk
  exact (F k).rescaledTerminalFlow_ball_volume_lower_bound
    (Q k) (hQ k) (τ k) (p k) r ν hk

end PoincareConjecture.RicciFlow
