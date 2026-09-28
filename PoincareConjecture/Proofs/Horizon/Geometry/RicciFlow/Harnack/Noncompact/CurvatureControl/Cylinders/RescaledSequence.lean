import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Components

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

noncomputable def rescaledTerminalFlow (F : RicciFlow n M J)
    (Q : ℝ) (hQ : 0 < Q) (τ : ℝ) :
    RicciFlow n M ((fun s : ℝ => τ + s / Q) ⁻¹' J) := by
  have hK : ((fun s : ℝ => τ + s / Q) ⁻¹' J).OrdConnected :=
    F.interval.preimage_mono
      (fun _ _ h => _root_.add_le_add le_rfl (div_le_div_of_nonneg_right h hQ.le))
  have hi (t : ℝ) : τ + Q * (t - τ) / Q = t := by field_simp; ring
  have hne : ((fun s : ℝ => τ + s / Q) ⁻¹' J).Nontrivial := by
    obtain ⟨s, hs, t, ht, hst⟩ := F.nontrivial
    refine ⟨Q * (s - τ), ?_, Q * (t - τ), ?_, ?_⟩
    · simpa only [mem_preimage, hi] using hs
    · simpa only [mem_preimage, hi] using ht
    · intro h
      apply hst
      nlinarith [hQ]
  exact F.parabolicRescale Q hQ τ (fun _ hs => hs) hK hne

theorem rescaledTerminalFlow_interior (_F : RicciFlow n M J)
    {Q τ a : ℝ} (hQ : 0 < Q)
    (hJ : Icc (τ + a / Q) τ ⊆ interior J) :
    Icc a 0 ⊆ interior ((fun s : ℝ => τ + s / Q) ⁻¹' J) := by
  intro s hs
  apply preimage_interior_subset_interior_preimage
    (show Continuous (fun s : ℝ => τ + s / Q) by fun_prop)
  apply hJ
  constructor
  · exact _root_.add_le_add le_rfl (div_le_div_of_nonneg_right hs.1 hQ.le)
  · simpa using _root_.add_le_add (le_refl τ) (div_le_div_of_nonneg_right hs.2 hQ.le)

@[simp] theorem rescaledTerminalFlow_scalar_zero (F : RicciFlow n M J)
    (Q : ℝ) (hQ : 0 < Q) (τ : ℝ) (p : M)
    (hbase : (F.connection τ).scalarCurvature p = Q) :
    ((F.rescaledTerminalFlow Q hQ τ).connection 0).scalarCurvature p = 1 := by
  change (rescaledMetric_connection _ _ Q hQ).scalarCurvature p = 1
  rw [rescaledMetric_scalarCurvature, zero_div, add_zero, hbase, inv_mul_cancel₀ hQ.ne']

theorem rescaledTerminalFlow_scalar_le_four (F : RicciFlow n M J)
    (Q : ℝ) (hQ : 0 < Q) (τ a L : ℝ) (p : M)
    (hscalar : ∀ t ∈ Icc (τ + a / Q) τ,
      ∀ x ∈ (F.metric τ).ball p (L / Real.sqrt Q),
        (F.connection t).scalarCurvature x ≤ 4 * Q) :
    ∀ s ∈ Icc a 0, ∀ x ∈ ((F.rescaledTerminalFlow Q hQ τ).metric 0).ball p L,
      ((F.rescaledTerminalFlow Q hQ τ).connection s).scalarCurvature x ≤ 4 := by
  intro s hs x hx
  change x ∈ (rescaledMetric (F.metric (τ + 0 / Q)) Q hQ).ball p L at hx
  rw [rescaledMetric_ball_allDimensions, zero_div, add_zero] at hx
  have ht : τ + s / Q ∈ Icc (τ + a / Q) τ := by
    constructor
    · exact _root_.add_le_add le_rfl (div_le_div_of_nonneg_right hs.1 hQ.le)
    · simpa using _root_.add_le_add (le_refl τ) (div_le_div_of_nonneg_right hs.2 hQ.le)
  change (rescaledMetric_connection _ _ Q hQ).scalarCurvature x ≤ 4
  rw [rescaledMetric_scalarCurvature]
  calc
    Q⁻¹ * (F.connection (τ + s / Q)).scalarCurvature x ≤ Q⁻¹ * (4 * Q) :=
      mul_le_mul_of_nonneg_left (hscalar _ ht x hx) (inv_nonneg.mpr hQ.le)
    _ = 4 := by field_simp

theorem rescaledTerminalFlow_unit_volume_lower_bound
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    (F : RicciFlow n M J) (Q : ℝ) (hQ : 0 < Q) (τ : ℝ) (p : M)
    {ν : ℝ}
    (hvolume : ENNReal.ofReal (ν * (1 / Real.sqrt Q) ^ n) ≤
      (F.metric τ).volumeMeasure ((F.metric τ).ball p (1 / Real.sqrt Q))) :
    ENNReal.ofReal ν ≤ ((F.rescaledTerminalFlow Q hQ τ).metric 0).volumeMeasure
      (((F.rescaledTerminalFlow Q hQ τ).metric 0).ball p 1) := by
  change ENNReal.ofReal ν ≤ (rescaledMetric (F.metric (τ + 0 / Q)) Q hQ).volumeMeasure
    ((rescaledMetric (F.metric (τ + 0 / Q)) Q hQ).ball p 1)
  rw [rescaledMetric_volumeMeasure, rescaledMetric_ball_allDimensions, zero_div, add_zero]
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (Real.sqrt Q) ^ n)) hvolume
  have hid : ENNReal.ofReal (Real.sqrt Q) ^ n *
      ENNReal.ofReal (ν * (1 / Real.sqrt Q) ^ n) = ENNReal.ofReal ν := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg Q),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) n)]
    congr 1
    have hne := (Real.sqrt_pos.mpr hQ).ne'
    calc
      Real.sqrt Q ^ n * (ν * (1 / Real.sqrt Q) ^ n) =
          ν * (Real.sqrt Q * (1 / Real.sqrt Q)) ^ n := by rw [mul_pow]; ring
      _ = ν := by simp [hne]
  rwa [hid] at h

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_nonflat_pointed_limit_of_rescaled_terminal_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{0} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (Q τ L : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k) {a ν : ℝ} (ha : a ≤ -2)
    (hJ : ∀ k, Icc (τ k + a / Q k) (τ k) ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (τ k + a / Q k) (τ k),
      MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (τ k + a / Q k) (τ k), ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hL : Tendsto L atTop atTop)
    (hscalar : ∀ k, ∀ t ∈ Icc (τ k + a / Q k) (τ k),
      ∀ x ∈ ((F k).metric (τ k)).ball (p k) (L k / Real.sqrt (Q k)),
        ((F k).connection t).scalarCurvature x ≤ 4 * Q k)
    (hnormalize : ∀ k, ((F k).connection (τ k)).scalarCurvature (p k) = Q k)
    (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal (ν * (1 / Real.sqrt (Q k)) ^ (m + 1)) ≤
      ((F k).metric (τ k)).volumeMeasure
        (((F k).metric (τ k)).ball (p k) (1 / Real.sqrt (Q k)))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : PointedGeometricConvergence
        (bufferedCylinderSequence C (fun k => (fun s : ℝ => τ k + s / Q k) ⁻¹' J k)
          (fun k => (F k).rescaledTerminalFlow (Q k) (hQ k) (τ k)) p a δ
          (by linarith) (fun k => (F k).rescaledTerminalFlow_interior (hQ k) (hJ k))),
        (∀ t ∈ Ioo (a + δ) δ,
          G.limitCarrier.metricComplete (G.limitFlow.metricAt t)) ∧
        0 < (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base ∧
        ∀ t ∈ Ioo (a + δ) δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤
            ((m + 1 : ℕ) : ℝ) ^ 2 * 4 := by
  have htime (k : ℕ) (s : ℝ) (hs : s ∈ Icc a 0) :
      τ k + s / Q k ∈ Icc (τ k + a / Q k) (τ k) := by
    constructor
    · exact _root_.add_le_add le_rfl (div_le_div_of_nonneg_right hs.1 (hQ k).le)
    · simpa using _root_.add_le_add (le_refl (τ k))
        (div_le_div_of_nonneg_right hs.2 (hQ k).le)
  apply exists_nonflat_pointed_limit_of_terminal_cylinders (ν := ν) hC hm C
    (fun k => (fun s : ℝ => τ k + s / Q k) ⁻¹' J k)
    (fun k => (F k).rescaledTerminalFlow (Q k) (hQ k) (τ k)) p ha
    (fun k => (F k).rescaledTerminalFlow_interior (hQ k) (hJ k))
    (fun k s hs => metricComplete_rescaledMetric _ (Q k) (hQ k)
      (hcomplete k _ (htime k s hs)))
    (fun k s hs x => rescaledMetric_nonnegativeCurvatureOperator _ _ (Q k) (hQ k) x
      (hoperator k _ (htime k s hs) x)) L hL
    (fun k => (F k).rescaledTerminalFlow_scalar_le_four
      (Q k) (hQ k) (τ k) a (L k) (p k) (hscalar k))
    (fun k => (F k).rescaledTerminalFlow_scalar_zero
      (Q k) (hQ k) (τ k) (p k) (hnormalize k)) hν
  filter_upwards [hvolume] with k hk
  exact (F k).rescaledTerminalFlow_unit_volume_lower_bound (Q k) (hQ k) (τ k) (p k) hk

end PoincareConjecture.RicciFlow
