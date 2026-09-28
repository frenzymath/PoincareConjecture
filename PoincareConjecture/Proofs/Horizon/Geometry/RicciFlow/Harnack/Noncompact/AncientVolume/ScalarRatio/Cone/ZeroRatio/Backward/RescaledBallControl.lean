import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Control

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem ancientRescaleAt_volume_lower_bound_of_scalar_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ}
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0)
    (a : ℝ) (ha : a ≤ 0) (q : M) {r A : ℝ} (hr : 0 < r)
    (hscalar : ∀ x ∈ ((F.ancientRescaleAt Q hQ t₀ ht₀).metric a).ball q r,
      ((F.ancientRescaleAt Q hQ t₀ ht₀).connection a).scalarCurvature x ≤ A)
    (hscale : (n : ℝ) ^ 2 * A ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (κ * r ^ n) ≤
      ((F.ancientRescaleAt Q hQ t₀ ht₀).metric a).volumeMeasure
        (((F.ancientRescaleAt Q hQ t₀ ht₀).metric a).ball q r) := by
  let G := F.ancientRescaleAt Q hQ t₀ ht₀
  have htime : t₀ + a / Q ≤ 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ha hQ.le)).trans ht₀
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hball : (G.metric a).ball q r =
      (F.metric (t₀ + a / Q)).ball q (r / Real.sqrt Q) := by
    rw [ancientRescaleAt_metric, rescaledMetric_ball_allDimensions]
  have hscalar' : ∀ x ∈ (F.metric (t₀ + a / Q)).ball q (r / Real.sqrt Q),
      (F.connection (t₀ + a / Q)).scalarCurvature x ≤ Q * A := by
    intro x hx
    have hh := hscalar x (hball.symm ▸ hx)
    rw [ancientRescaleAt_scalarCurvature] at hh
    have hmul := mul_le_mul_of_nonneg_left hh hQ.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] using hmul
  have hscale' : (n : ℝ) ^ 2 * (Q * A) ≤ (r / Real.sqrt Q)⁻¹ ^ 2 := by
    calc
      _ = Q * ((n : ℝ) ^ 2 * A) := by ring
      _ ≤ Q * r⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hscale hQ.le
      _ = _ := by rw [inv_div, div_pow, Real.sq_sqrt hQ.le, div_eq_mul_inv, inv_pow]
  have hvolume := F.ball_volume_lower_bound_of_bounded_ancient_terminal_scalar
    hC hcomplete hoperator hK hbound hnoncollapse htime q (div_pos hr hsq) hscalar' hscale'
  rw [ancientRescaleAt_metric, rescaledMetric_volumeMeasure, rescaledMetric_ball_allDimensions]
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal (Real.sqrt Q) ^ n)) hvolume
  have hid : ENNReal.ofReal (Real.sqrt Q) ^ n *
      ENNReal.ofReal (κ * (r / Real.sqrt Q) ^ n) = ENNReal.ofReal (κ * r ^ n) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg Q),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) n)]
    congr 1
    calc
      Real.sqrt Q ^ n * (κ * (r / Real.sqrt Q) ^ n) =
          κ * (Real.sqrt Q * (r / Real.sqrt Q)) ^ n := by rw [mul_pow]; ring
      _ = κ * r ^ n := by rw [mul_div_cancel₀ _ hsq.ne']
  rwa [hid] at hh

end PoincareConjecture.RicciFlow
