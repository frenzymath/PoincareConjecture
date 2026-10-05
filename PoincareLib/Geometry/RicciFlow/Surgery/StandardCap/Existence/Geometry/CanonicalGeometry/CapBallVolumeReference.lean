import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CapBallVolumeRadius
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.CalibratedBishopGromov

/-!
# Actual lower volume on a fixed reference core ball

The old normalized-ball witness and nonnegative-Ricci Bishop--Gromov
give the same lower volume ratio at every smaller positive radius.
Source: Morgan--Tian Definition 9.72(7), pp. 230-231, and Theorem 12.28,
pp. 323-324; cap-ball-volume.md, section 3.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.RiemannianMetric

/-- Actual nonnegative-Ricci Bishop--Gromov propagates a lower calibrated
volume ratio from one positive radius to every smaller positive radius,
in any positive dimension (Theorem 12.28). -/
theorem calibrated_small_ball_volume_lower_of_nonnegative_ricci
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (y : M) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
    {A : ℝ≥0∞}
    (hlower : A * ENNReal.ofReal s ^ n ≤ calibratedMetricVolume g (g.ball y s)) :
    A * ENNReal.ofReal r ^ n ≤ calibratedMetricVolume g (g.ball y r) := by
  have hs0 : ENNReal.ofReal s ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hs).ne'
  have hst : ENNReal.ofReal s ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hr0 : ENNReal.ofReal r ^ n ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne'
  have hrt : ENNReal.ofReal r ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hmono := M34.calibrated_ball_volume_ratio_antitoneOn_of_precompact g D y hn
    (mul_pos two_pos hs)
    (Proofs.M09.isCompact_closure_metric_ball g hcomplete y (2 * s))
    (fun x _ v => hRic x v)
  have hratio : calibratedMetricVolume g (g.ball y s) / ENNReal.ofReal s ^ n ≤
      calibratedMetricVolume g (g.ball y r) / ENNReal.ofReal r ^ n :=
    hmono ⟨hr, by linarith⟩ ⟨hs, by linarith⟩ hrs
  have hlarge : A ≤ calibratedMetricVolume g (g.ball y s) / ENNReal.ofReal s ^ n :=
    (ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl hst)).mpr hlower
  exact (ENNReal.le_div_iff_mul_le (Or.inl hr0) (Or.inl hrt)).mp (hlarge.trans hratio)

end PoincareMT.RiemannianMetric

namespace PoincareMT.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

/-- Actual Bishop--Gromov propagates the supplied core-ball volume
witness to every positive smaller radius (Definition 9.72(7)). -/
theorem small_core_ball_volume_lower
    (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ v : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x v v)
    {C : ℝ} (hC : N.cap_constant ≤ C) {y : M} (hy : y ∈ N.core)
    {r : ℝ} (hr : 0 < r) (hrr : r ≤ N.core_radius y) :
    ENNReal.ofReal (C⁻¹ * r ^ 3) ≤ calibratedMetricVolume g (g.ball y r) := by
  have hCpos : 0 < C := N.cap_constant_pos.trans_le hC
  have hr0 : 0 < N.core_radius y := N.core_radius_pos y hy
  obtain ⟨b, hb, hvol⟩ := N.core_ball_volume_lower
  have hbc : C⁻¹ ≤ b :=
    ((inv_le_inv₀ hCpos N.cap_constant_pos).mpr hC).trans hb.le
  have hbase : ENNReal.ofReal (C⁻¹) * ENNReal.ofReal (N.core_radius y) ^ 3 ≤
      calibratedMetricVolume g (g.ball y (N.core_radius y)) := by
    rw [← ENNReal.ofReal_pow hr0.le, ← ENNReal.ofReal_mul (inv_nonneg.mpr hCpos.le)]
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hbc (by positivity))).trans (hvol y hy)
  have hsmall : ENNReal.ofReal (C⁻¹) * ENNReal.ofReal r ^ 3 ≤
      calibratedMetricVolume g (g.ball y r) :=
    g.calibrated_small_ball_volume_lower_of_nonnegative_ricci N.connection
      (by norm_num) hcomplete hRic y hr hr0 hrr hbase
  rwa [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (inv_nonneg.mpr hCpos.le)] at hsmall

/-- One radius chosen from C before every normalized cap and core point
has a uniform actual calibrated lower volume (Theorem 12.28). -/
theorem reference_core_ball_volume_lower
    (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ v : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x v v)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    {C : ℝ} (hC : N.cap_constant ≤ C) (hC1 : 1 ≤ C) {y : M} (hy : y ∈ N.core) :
    ENNReal.ofReal (C⁻¹ * ((100 * C)⁻¹) ^ 3) ≤
      calibratedMetricVolume g (g.ball y ((100 * C)⁻¹)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hh : 0 < (100 * C)⁻¹ := by positivity
  have hhC : (100 * C)⁻¹ ≤ C⁻¹ :=
    (inv_le_inv₀ (by positivity) hCpos).mpr (by linarith)
  exact N.small_core_ball_volume_lower hcomplete hRic hC hy hh
    (hhC.trans (N.core_radius_bounds_of_normalized_base ho hnormal hC hC1 hy).1)

end PoincareMT.CapCertificate
