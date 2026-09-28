import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingGeometry
import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingScalar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g) (Q : ℝ) (hQ : 0 < Q)

omit [T2Space M] in
private theorem carrier_nonempty_for_scaling : N.carrier.Nonempty :=
  ⟨N.end_neck.center, N.end_neck_subset
    (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)⟩

theorem scaleMetric_intrinsic_diameter_bound :
    intrinsicDiameter (M13.scaleSmoothMetric g Q hQ) N.carrier <
      ENNReal.ofReal (N.cap_constant * scalarCurvatureSupOn
        (M13.scaleSmoothMetric g Q hQ) (M13.scaleLeviCivitaData N.connection Q hQ)
        N.carrier ^ (-1 / 2 : ℝ)) := by
  have hne := N.carrier_nonempty_for_scaling
  have hs := N.scalarSup_pos_on_subset subset_rfl hne
  rw [M13.scaleSmoothMetric_intrinsicDiameter,
    M13.scaleSmoothMetric_scalarCurvatureSupOn_rpow N.connection Q hQ N.carrier hs.le,
    show -(-1 / 2 : ℝ) = 1 / 2 by ring, ← Real.sqrt_eq_rpow,
    mul_left_comm N.cap_constant, ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
  exact (ENNReal.mul_right_strictMono
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne' ENNReal.ofReal_ne_top)
    N.intrinsic_diameter_bound

theorem scaleMetric_volume_bound :
    calibratedMetricVolume (M13.scaleSmoothMetric g Q hQ) N.carrier <
      ENNReal.ofReal N.cap_constant * ENNReal.ofReal (scalarCurvatureSupOn
        (M13.scaleSmoothMetric g Q hQ) (M13.scaleLeviCivitaData N.connection Q hQ)
        N.carrier ^ (-3 / 2 : ℝ)) := by
  have hne := N.carrier_nonempty_for_scaling
  have hs := N.scalarSup_pos_on_subset subset_rfl hne
  rw [M13.scaleSmoothMetric_volume,
    M13.scaleSmoothMetric_scalarCurvatureSupOn_rpow N.connection Q hQ N.carrier hs.le,
    show -(-3 / 2 : ℝ) = 3 / 2 by ring,
    ENNReal.ofReal_mul (Real.rpow_nonneg hQ.le _), mul_left_comm]
  exact (ENNReal.mul_right_strictMono
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hQ _)).ne' ENNReal.ofReal_ne_top)
    N.volume_bound

theorem scaleMetric_core_radius_eq {y : M} (hy : y ∈ N.core) :
    scalarCurvatureSupOn (M13.scaleSmoothMetric g Q hQ)
      (M13.scaleLeviCivitaData N.connection Q hQ)
      (RiemannianMetric.ball (M13.scaleSmoothMetric g Q hQ) y
        (Real.sqrt Q * N.core_radius y)) =
      (Real.sqrt Q * N.core_radius y)⁻¹ ^ 2 := by
  rw [M13.scaleSmoothMetric_ball,
    M13.scaleSmoothMetric_scalarCurvatureSupOn N.connection Q hQ,
    N.core_radius_eq y hy]
  simp only [mul_inv_rev, mul_pow, inv_pow, Real.sq_sqrt hQ.le, div_eq_mul_inv]

omit [T2Space M] in

theorem scaleMetric_core_ball_volume_lower :
    ∃ bound : ℝ, N.cap_constant⁻¹ < bound ∧ ∀ y ∈ N.core,
      ENNReal.ofReal (bound * (Real.sqrt Q * N.core_radius y) ^ 3) ≤
        calibratedMetricVolume (M13.scaleSmoothMetric g Q hQ)
          (RiemannianMetric.ball (M13.scaleSmoothMetric g Q hQ) y
            (Real.sqrt Q * N.core_radius y)) := by
  obtain ⟨b, hb, hvolume⟩ := N.core_ball_volume_lower
  refine ⟨b, hb, ?_⟩
  intro y hy
  have hpow : Q ^ (3 / 2 : ℝ) = (Real.sqrt Q) ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hQ,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    calc
      Q * Real.sqrt Q = (Real.sqrt Q) ^ 2 * Real.sqrt Q := by rw [Real.sq_sqrt hQ.le]
      _ = _ := by ring
  rw [M13.scaleSmoothMetric_ball, M13.scaleSmoothMetric_volume]
  simp only [Real.rpow_eq_pow, Nat.cast_ofNat]
  rw [hpow, mul_pow,
    mul_left_comm b, ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) 3)]
  exact mul_le_mul_right (hvolume y hy) _

theorem scaleMetric_gradient_bound :
    ∃ bound : ℝ, bound < N.cap_constant ∧ ∀ x ∈ N.carrier,
      scalarGradientNorm (M13.scaleSmoothMetric g Q hQ)
        (M13.scaleLeviCivitaData N.connection Q hQ) x ≤
          bound * (M13.scaleLeviCivitaData N.connection Q hQ).scalarCurvature x ^
            (3 / 2 : ℝ) := by
  obtain ⟨b, hb, hgradient⟩ := N.gradient_bound
  refine ⟨b, hb, ?_⟩
  intro x hx
  rw [M13.scaleSmoothMetric_scalarGradientNorm, M13.scaleLeviCivitaData_scalarCurvature,
    Real.div_rpow (N.scalar_pos x hx).le hQ.le]
  calc
    _ ≤ (b * N.connection.scalarCurvature x ^ (3 / 2 : ℝ)) / Q ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_right (hgradient x hx) (Real.rpow_pos_of_pos hQ _).le
    _ = _ := by ring

theorem scaleMetric_laplacian_bound :
    ∃ bound : ℝ, bound < N.cap_constant ∧ ∀ x ∈ N.carrier,
      |(M13.scaleLeviCivitaData N.connection Q hQ).laplacian
          (M13.scaleLeviCivitaData N.connection Q hQ).scalarCurvature x +
        2 * (M13.scaleLeviCivitaData N.connection Q hQ).ricciNormSq x| ≤
          bound * (M13.scaleLeviCivitaData N.connection Q hQ).scalarCurvature x ^ 2 := by
  obtain ⟨b, hb, hevolution⟩ := N.laplacian_bound
  refine ⟨b, hb, ?_⟩
  intro x hx
  rw [M13.scaleLeviCivitaData_scalarEvolution, M13.scaleLeviCivitaData_scalarCurvature,
    abs_div, abs_of_pos (sq_pos_of_pos hQ), div_pow]
  calc
    _ ≤ (b * N.connection.scalarCurvature x ^ 2) / Q ^ 2 :=
      div_le_div_of_nonneg_right (hevolution x hx) (sq_nonneg Q)
    _ = _ := by ring

end PoincareConjecture.CapCertificate
