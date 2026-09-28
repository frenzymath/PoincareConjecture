import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.InitialFlowExistence
import PoincareConjecture.Proofs.M45.Sec15_2_Constants.ProducerEndpoints
import PoincareConjecture.Proofs.M15.Thm8_10_EarlyVolume










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M45



theorem normalized_initial_ball_lower_bound
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] (N : NormalizedInitialMetric (M := M))
    (x : M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((euclideanUnitBallLebesgueVolume.toReal / 2) * r ^ 3) ≤
      calibratedMetricVolume N.metric (N.metric.ball x r) := by
  have hfinite : euclideanUnitBallLebesgueVolume ≠ ⊤ :=
    Metric.isBounded_ball.measure_lt_top.ne
  have hcoeff : ENNReal.ofReal ((euclideanUnitBallLebesgueVolume.toReal / 2) * r ^ 3) =
      (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 := by
    rw [ENNReal.ofReal_mul (div_nonneg ENNReal.toReal_nonneg (by norm_num)),
      ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal hfinite,
      ENNReal.ofReal_pow hr.le]
    norm_num only [ENNReal.ofReal_ofNat]
  rw [hcoeff]
  have hvolume : calibratedMetricVolume N.metric = normalizedMetricVolume N.metric := rfl
  rw [hvolume, ← N.volume_is_normalized_metric]
  exact N.small_ball_lower_bound x r hr hr1



theorem initialFlowProducer
    (h03 : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [CompactSpace M], RicciFlowLocalTheory 3 M) :
    InitialFlowProducer.{u} := by
  let v := euclideanUnitBallLebesgueVolume.toReal / 2
  let C := Real.exp (3 / 8 : ℝ)
  have hv : 0 < v := by
    apply div_pos _ (by norm_num)
    apply ENNReal.toReal_pos
    · exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin 3))
        (by norm_num : (0 : ℝ) < 1)).ne'
    · exact Metric.isBounded_ball.measure_lt_top.ne
  have hC : 1 ≤ C := Real.one_le_exp (by norm_num)
  have hCp : 0 < C := Real.exp_pos _
  intro epsilon _hepsilon hepsilonLe
  refine ⟨v / C ^ 6, div_pos hv (pow_pos hCp _), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ N
  obtain ⟨F, hF0, hD0, hRm⟩ := exists_initial_flow_with_curvature
    (h03 M) N.metric N.connection N.full_curvature_bound
  refine ⟨F, hF0, hD0, hRm, ?_⟩
  intro t ht x r hr hrepsilon
  have hr1 : r ≤ 1 := hrepsilon.trans (hepsilonLe.trans (by norm_num))
  have hnorm (q : M) (w : TangentSpace (𝓡 3) q) :=
    M04.tangentNorm_comparison_at_of_curvature_bound F (by norm_num) ht ht.1
      (by norm_num : (0 : ℝ) ≤ 2) q
      (fun s hs => hRm s ⟨hs.1, hs.2.trans ht.2⟩ q) w
  have hexp : Real.exp ((3 : ℝ) * 2 * (t - 0)) ≤ C := by
    apply Real.exp_le_exp.mpr
    linarith [ht.2]
  apply Proofs.M15.calibrated_ball_lower_bound_of_tangentNorm_comparison
    (F.metric 0) (F.metric t) x hC hv.le hr hr1
  · intro q w
    exact (hnorm q w).2.trans
      (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))
  · intro q w
    have h := mul_le_mul_of_nonneg_left (hnorm q w).1
      (Real.exp_pos ((3 : ℝ) * 2 * (t - 0))).le
    simp only [Nat.cast_ofNat] at h
    have he : Real.exp ((3 : ℝ) * 2 * (t - 0)) *
        Real.exp (-(3 : ℝ) * 2 * (t - 0)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [← mul_assoc, he, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))
  · intro s hs hs1
    rw [hF0]
    exact normalized_initial_ball_lower_bound N x hs hs1

end PoincareConjecture.M45
