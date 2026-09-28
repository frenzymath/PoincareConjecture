import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_CapCore
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_VolumeBoundary
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Thm1_34_ModelVolume
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SmallCurvature










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M46


noncomputable def canonicalCapLoss : ℝ := (Real.cosh 8)⁻¹ ^ 2


theorem canonicalCapLoss_bounds : 0 < canonicalCapLoss ∧ canonicalCapLoss ≤ 1 := by
  refine ⟨pow_pos (inv_pos.mpr (Real.cosh_pos 8)) _, ?_⟩
  exact pow_le_one₀ (inv_nonneg.mpr (Real.cosh_pos 8).le)
    ((inv_le_one₀ (Real.cosh_pos 8)).mpr (Real.one_le_cosh 8))


noncomputable def canonicalCapVolumeFloor (B : ℝ) : ℝ := canonicalCapLoss / (27 * B ^ 4)


theorem canonicalCapVolumeFloor_pos {B : ℝ} (hB : 1 ≤ B) :
    0 < canonicalCapVolumeFloor B :=
  div_pos canonicalCapLoss_bounds.1 (mul_pos (by norm_num)
    (pow_pos (zero_lt_one.trans_le hB) _))



theorem canonical_controlled_ball_volume
    {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (x : M)
    {A R s k : ℝ} (hA : 0 < A) (hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R) (hk : 0 < k)
    (hcompact : IsCompact (closure (g.ball x R)))
    (hcurv : ∀ y ∈ g.ball x R, D.curvatureTensorNorm y ≤ (A / R) ^ 2)
    (hvolume : ENNReal.ofReal (k * R ^ 3) ≤ calibratedMetricVolume g (g.ball x R)) :
    ENNReal.ofReal ((Real.cosh A)⁻¹ ^ 2 * k * s ^ 3) ≤
      calibratedMetricVolume g (g.ball x s) := by
  rw [M15.calibratedMetricVolume_eq_volumeMeasure] at hvolume ⊢
  have hcompare := canonical_smallBall_volume_at_boundary g x (by norm_num)
    (sq_nonneg (A / R)) hs hsR hcompact D
    (fun y hy v => D.ricci_quadratic_lower_bound_of_curvatureTensorNorm_le y (hcurv y hy) v)
  apply (ENNReal.ofReal_le_ofReal (scaled_smallBallVolumeBound_ge hA hR hs hk)).trans
  unfold RiemannianMetric.smallerBallVolumeBound
  rw [ENNReal.ofReal_mul (div_nonneg
      (RiemannianMetric.modelVolume_pos (by norm_num : 1 ≤ 3) (sq_nonneg (A / R)) hs).le
      (RiemannianMetric.modelVolume_pos (by norm_num : 1 ≤ 3) (sq_nonneg (A / R)) hR).le),
    ENNReal.ofReal_div_of_pos
      (RiemannianMetric.modelVolume_pos (by norm_num : 1 ≤ 3) (sq_nonneg (A / R)) hR)]
  exact (mul_le_mul' le_rfl hvolume).trans hcompare


theorem canonicalCap_core_curvature (P : M46Predecessors.{u})
    {M : Type u} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    {x : M} (hx : x ∈ N.core) {t : ℝ}
    (hpinch : SurgeryPinchedAt N.connection t) (hsmall : N.core_radius x ≤ 1 / 200)
    {y : M} (hy : y ∈ g.ball x (N.core_radius x)) :
    N.connection.curvatureTensorNorm y ≤ (8 / N.core_radius x) ^ 2 := by
  have hq := N.core_radius_pos x hx
  have hscalar := (canonicalCap_core_scalar_bounds N hx (le_refl N.cap_constant)).1 y hy
  have hmax : max (N.connection.scalarCurvature y) (Real.exp 4) ≤
      4 * (N.core_radius x)⁻¹ ^ 2 :=
    max_le (hscalar.trans (by nlinarith [sq_nonneg (N.core_radius x)⁻¹]))
      (exp_four_le_four_inv_sq hq hsmall)
  have hnorm := pinched_curvature_norm_le P hpinch (mem_univ y)
  calc
    N.connection.curvatureTensorNorm y ≤ 52 * (N.core_radius x)⁻¹ ^ 2 := by nlinarith
    _ ≤ 64 * (N.core_radius x)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, mul_pow]; norm_num



theorem canonicalCap_test_ball_volume (P : M46Predecessors.{u})
    {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    {x : M} (hx : x ∈ N.core) {t B s : ℝ}
    (hB1 : 1 ≤ B) (hB : N.cap_constant ≤ B) (hs : 0 < s)
    (hpinch : SurgeryPinchedAt N.connection t) (hsmall : N.core_radius x ≤ 1 / 200)
    (hscalar : N.connection.scalarCurvature x ≤ 9 * s⁻¹ ^ 2) :
    ENNReal.ofReal (canonicalCapVolumeFloor B * s ^ 3) ≤ calibratedMetricVolume g (g.ball x s) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hq := N.core_radius_pos x hx
  have hvolume := canonicalCap_core_volume N hx hB
  have hloss := canonicalCapLoss_bounds
  rcases le_total s (N.core_radius x) with hs_le | hq_le
  · have h := canonical_controlled_ball_volume g N.connection x (by norm_num : (0 : ℝ) < 8)
      hq hs hs_le (inv_pos.mpr hBpos) (N.core_ball_compact x hx)
      (fun y hy => canonicalCap_core_curvature P N hx hpinch hsmall hy) hvolume
    apply le_trans (ENNReal.ofReal_le_ofReal _) h
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hs.le 3)
    unfold canonicalCapVolumeFloor
    change canonicalCapLoss / (27 * B ^ 4) ≤ canonicalCapLoss * B⁻¹
    rw [← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left hloss.1.le hBpos
    have hpow := one_le_pow₀ hB1 (n := 3)
    nlinarith
  · have hscale := canonicalCap_test_radius_le N hx hB1 hB hs hscalar
    have hcube := pow_le_pow_left₀ hs.le hscale 3
    have hnum : canonicalCapLoss * s ^ 3 ≤ 27 * B ^ 3 * N.core_radius x ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hloss.2 (pow_nonneg hs.le 3)
      nlinarith
    have hbound : canonicalCapVolumeFloor B * s ^ 3 ≤ B⁻¹ * N.core_radius x ^ 3 := by
      unfold canonicalCapVolumeFloor
      field_simp [hBpos.ne']
      nlinarith
    apply (ENNReal.ofReal_le_ofReal hbound).trans
    apply hvolume.trans
    apply measure_mono
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal hq_le)

end PoincareConjecture.Proofs.M46
