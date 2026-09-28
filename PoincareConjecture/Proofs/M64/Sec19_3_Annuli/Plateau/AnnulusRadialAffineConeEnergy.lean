import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialAffineCone

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64EuclideanEnergyDensity (f : LoopPlane → E) (z : LoopPlane) :
    m60EnergyDensity (RiemannianMetric.euclideanMetric m) f z =
      (‖fderiv ℝ f z (EuclideanSpace.single (0 : Fin 2) 1)‖ ^ 2 +
        ‖fderiv ℝ f z (EuclideanSpace.single (1 : Fin 2) 1)‖ ^ 2) / 2 := by
  simp +instances only [m60EnergyDensity, Matrix.trace_fin_two, m60AreaGram,
    RiemannianMetric.euclideanMetric_inner,
    mfderiv_eq_fderiv, EuclideanSpace.basisFun_apply, real_inner_self_eq_norm_sq]
  change (1 / 2 : ℝ) *
    (‖fderiv ℝ f z (EuclideanSpace.single (0 : Fin 2) 1)‖ ^ 2 +
      ‖fderiv ℝ f z (EuclideanSpace.single (1 : Fin 2) 1)‖ ^ 2) = _
  ring

theorem m64Euclidean_curve_speed (w : ℝ → E) (t : ℝ) :
    (RiemannianMetric.euclideanMetric m).tangentNorm (w t) (curveVelocity w t) =
      ‖deriv w t‖ := by
  have hv : curveVelocity w t = deriv w t := by
    simpa +instances only [curveVelocity, mfderiv_eq_fderiv] using!
      (fderiv_apply_one_eq_deriv : fderiv ℝ w t 1 = deriv w t)
  simp +instances only [hv, RiemannianMetric.euclideanMetric_tangentNorm]

theorem m64EuclideanInterpolator_last_column_bound {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (p q v : E) :
    (RiemannianMetric.euclideanMetric m).tangentNorm (m64EuclideanInterpolator (s, p, q))
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 m).prod (𝓡 m))) (𝓡 m) m64EuclideanInterpolator
        (s, p, q) (0, 0, v)) ≤
      1 * (RiemannianMetric.euclideanMetric m).tangentNorm q v := by
  rw [m64EuclideanInterpolator_last_column]
  have hnorm : ‖s • v‖ ≤ 1 * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs.1, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2
  simpa +instances only [RiemannianMetric.euclideanMetric_tangentNorm] using! hnorm

theorem m64EuclideanCone_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ℝ → E), ContDiff ℝ 1 w →
      Function.Periodic w curvePeriod → ∀ i : Fin 2,
        (∫ z in ball (0 : LoopPlane) 1,
          ‖fderiv ℝ (m64EuclideanCone w) z (EuclideanSpace.single i 1)‖ ^ 2) ≤
          C * ∫ t in Icc (0 : ℝ) curvePeriod, ‖deriv w t‖ ^ 2 := by
  obtain ⟨P, _, hP⟩ := exists_diskTimeProfile_derivative_bound
  let A : ℝ := P ^ 2 / 2 * curvePeriod ^ 2 + 2
  refine ⟨2 * A, by dsimp only [A]; positivity, ?_⟩
  intro w hw hperiod i
  have hFc := m64EuclideanCone_contDiff hw hperiod
  have hF : ContMDiff (𝓡 2) (𝓡 m) 1 (m64EuclideanCone w) := hFc.contMDiff
  have he := m64LocalConeDiskMap_energy_le (RiemannianMetric.euclideanMetric m)
    m64EuclideanInterpolator w hw.contMDiff hperiod
    (fun t => by simp [m64EuclideanInterpolator]) hF
    (fun _ _ _ => (m64EuclideanInterpolator_contMDiff (m := m)).contMDiffAt)
    (fun s _ t => m64EuclideanInterpolator_speed s (w 0) (w t))
    (B := 1) (fun _ hs t v =>
      m64EuclideanInterpolator_last_column_bound hs (w 0) (w t) v) hP
  simp only [one_pow, mul_one, m64Euclidean_curve_speed] at he
  have hE : IntegrableOn (m60EnergyDensity (RiemannianMetric.euclideanMetric m)
      (m64EuclideanCone w)) loopDiskSet volume :=
    (m60EnergyDensity_continuous _ hF).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1)
  have hcol : IntegrableOn (fun z =>
      ‖fderiv ℝ (m64EuclideanCone w) z (EuclideanSpace.single i 1)‖ ^ 2)
        (ball (0 : LoopPlane) 1) volume := by
    have hc : Continuous (fun z => fderiv ℝ (m64EuclideanCone w) z (EuclideanSpace.single i 1)) :=
      (hFc.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  calc
    _ ≤ ∫ z in ball (0 : LoopPlane) 1,
        2 * m60EnergyDensity (RiemannianMetric.euclideanMetric m) (m64EuclideanCone w) z := by
      apply integral_mono hcol ((hE.mono_set ball_subset_closedBall).const_mul 2)
      intro z
      change ‖fderiv ℝ (m64EuclideanCone w) z (EuclideanSpace.single i 1)‖ ^ 2 ≤
        2 * m60EnergyDensity (RiemannianMetric.euclideanMetric m) (m64EuclideanCone w) z
      rw [m64EuclideanEnergyDensity]
      have hsq (x y : ℝ) : x ^ 2 ≤ 2 * ((x ^ 2 + y ^ 2) / 2) := by
        nlinarith only [sq_nonneg y]
      fin_cases i
      · simpa +instances only using! hsq
          ‖fderiv ℝ (m64EuclideanCone w) z (EuclideanSpace.single (0 : Fin 2) 1)‖
          ‖fderiv ℝ (m64EuclideanCone w) z (EuclideanSpace.single (1 : Fin 2) 1)‖
      · simpa +instances only [add_comm] using! hsq
          ‖fderiv ℝ (m64EuclideanCone w) z (EuclideanSpace.single (1 : Fin 2) 1)‖
          ‖fderiv ℝ (m64EuclideanCone w) z (EuclideanSpace.single (0 : Fin 2) 1)‖
    _ = 2 * ∫ z in ball (0 : LoopPlane) 1,
        m60EnergyDensity (RiemannianMetric.euclideanMetric m) (m64EuclideanCone w) z :=
      integral_const_mul _ _
    _ ≤ 2 * ∫ z in loopDiskSet,
        m60EnergyDensity (RiemannianMetric.euclideanMetric m) (m64EuclideanCone w) z :=
      mul_le_mul_of_nonneg_left (setIntegral_mono_set hE
        (Eventually.of_forall (m60EnergyDensity_nonneg _ _))
        (Eventually.of_forall fun z hz => ball_subset_closedBall hz)) (by norm_num)
    _ ≤ 2 * (A * ∫ t in Icc (0 : ℝ) curvePeriod, ‖deriv w t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

end PoincareConjecture
