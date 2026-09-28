import PoincareConjecture.Proofs.M10.CalibratedTransport
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M34



theorem compact_identity_metric_bounds {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    ∃ b j : ℝ, 0 < b ∧ 0 < j ∧ ∀ x ∈ K,
      ‖M10.pullbackMetricForm g id x‖ ≤ b ∧ j ≤ M10.pullbackJacobian g id x := by
  have hB : Continuous (M10.pullbackMetricForm g id) :=
    continuous_iff_continuousAt.mpr fun _ =>
      M10.pullbackMetricForm_continuousAt g contMDiffAt_id
  have hJ : Continuous (M10.pullbackJacobian g id) :=
    continuous_iff_continuousAt.mpr fun _ =>
      M10.pullbackJacobian_continuousAt g contMDiffAt_id
  have hpos (x : EuclideanSpace ℝ (Fin n)) : 0 < M10.pullbackJacobian g id x := by
    apply M10.pullbackJacobian_pos
    rw [mfderiv_id]
    exact fun _ _ h => h
  have hBn : Continuous (fun x => ‖M10.pullbackMetricForm g id x‖) := by
    let : NormedAddCommGroup
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := inferInstance
    apply Continuous.comp (g := norm) _ hB
    exact continuous_norm
  obtain ⟨A, hA⟩ := hK.bddAbove_image hBn.continuousOn
  obtain ⟨B, hBinv⟩ := hK.bddAbove_image
    (hJ.inv₀ (fun x => (hpos x).ne')).continuousOn
  let b : ℝ := max 1 A
  let d : ℝ := max 1 B
  have hb : 0 < b := zero_lt_one.trans_le (le_max_left _ _)
  have hd : 0 < d := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨b, d⁻¹, hb, inv_pos.mpr hd, fun x hx => ?_⟩
  refine ⟨(hA ⟨x, hx, rfl⟩).trans (le_max_right _ _), ?_⟩
  apply (inv_le_comm₀ hd (hpos x)).mpr
  exact (hBinv ⟨x, hx, rfl⟩).trans (le_max_right _ _)



theorem coordinate_ball_volume_lower {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric n M)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {r j : ℝ} (hsource : Metric.ball 0 r ⊆ e.source)
    (hjac : ∀ x ∈ Metric.ball 0 r, j ≤ M10.pullbackJacobian g e x) :
    ENNReal.ofReal j * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤
      calibratedMetricVolume g (e '' Metric.ball 0 r) := by
  have hvol : calibratedMetricVolume g (e '' Metric.ball 0 r) =
      ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
        ENNReal.ofReal (M10.pullbackJacobian g e x) := by
    convert! M10.calibratedMetricVolume_image_eq_lintegral g e.toOpenPartialHomeomorph
      (e.contMDiffOn_toFun.of_le (by simp)) (e.contMDiffOn_invFun.of_le (by simp))
      measurableSet_ball hsource using 1
  rw [hvol]
  calc
    _ = ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, ENNReal.ofReal j := by
      simp
    _ ≤ _ := setLIntegral_mono' measurableSet_ball
      (fun x hx => ENNReal.ofReal_le_ofReal (hjac x hx))

end PoincareConjecture.M34
