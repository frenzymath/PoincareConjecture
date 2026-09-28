import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Selection









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem m23_recentered_volume_lower_bound
    (P : M23NormalizedKappaCompactnessPredecessors) (K : AncientKappaSolution 3 M)
    (p q : M) {r ν : ℝ} (hr : 0 < r) (hν : 0 ≤ ν)
    (hq : q ∈ (K.flow.metric 0).ball p (2 * r))
    (hvolume : ENNReal.ofReal (ν * r ^ 3) ≤
      calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r)) :
    ∀ a : ℝ, 0 < a → a ≤ 3 * r →
      ENNReal.ofReal ((ν / 27) * a ^ 3) ≤
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball q a) := by
  let g := K.flow.metric 0
  let := g.toMetricSpace
  have hqdist : dist p q < 2 * r := by
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm] at hq
    exact hq
  have hsubset : g.ball p r ⊆ g.ball q (3 * r) := by
    rw [← g.toMetricSpace_ball, ← g.toMetricSpace_ball]
    intro y hy
    have hpy : dist p y < r := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hy
    rw [Metric.mem_ball, dist_comm]
    linarith [dist_triangle q p y, dist_comm q p]
  have hlarge : ENNReal.ofReal (ν * r ^ 3) ≤
      calibratedMetricVolume g (g.ball q (3 * r)) :=
    hvolume.trans (MeasureTheory.measure_mono hsubset)
  have hratio : ENNReal.ofReal (ν / 27) ≤
      metricBallVolumeRatio g q ⟨3 * r, by positivity⟩ := by
    have h := ENNReal.div_le_div_right hlarge (ENNReal.ofReal (3 * r) ^ 3)
    have hcancel : ν * r ^ 3 / (3 * r) ^ 3 = ν / 27 := by
      field_simp
      ring
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 3 * r),
      ← ENNReal.ofReal_div_of_pos (by positivity : 0 < (3 * r) ^ 3), hcancel] at h
    simpa only [metricBallVolumeRatio, ENNReal.ofReal_pow (by positivity : 0 ≤ 3 * r)] using h
  intro a ha har
  have hsmall : ENNReal.ofReal (ν / 27) ≤ metricBallVolumeRatio g q ⟨a, ha⟩ :=
    hratio.trans (P.ratio_antitone M K 0 le_rfl q
      (show (⟨a, ha⟩ : PositiveRadius) ≤ ⟨3 * r, by positivity⟩ from har))
  have hden0 : ENNReal.ofReal a ^ 3 ≠ 0 := pow_ne_zero _ (by positivity)
  have hdentop : ENNReal.ofReal a ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h := (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdentop)).mp hsmall
  rw [ENNReal.ofReal_mul (div_nonneg hν (by norm_num : (0 : ℝ) ≤ 27)),
    ENNReal.ofReal_pow ha.le]
  exact h




theorem m23_exists_backward_controlled_point_with_volume
    (P : M23NormalizedKappaCompactnessPredecessors) (K : AncientKappaSolution 3 M)
    (p x : M) {r ν : ℝ} (hr : 0 < r) (hν : 0 ≤ ν)
    (hx : x ∈ (K.flow.metric 0).ball p r)
    (hvolume : ENNReal.ofReal (ν * r ^ 3) ≤
      calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r)) :
    ∃ q : M, ∃ s : ℝ, q ∈ (K.flow.metric 0).ball p (2 * r) ∧
      0 < s ∧ s ≤ r ∧
      (K.flow.connection 0).scalarCurvature x ≤ (K.flow.connection 0).scalarCurvature q ∧
      s * Real.sqrt ((K.flow.connection 0).scalarCurvature q) =
        r * Real.sqrt ((K.flow.connection 0).scalarCurvature x) / 2 ∧
      (∀ t : ℝ, t ≤ 0 → ∀ y ∈ (K.flow.metric 0).ball q s,
        |(K.flow.connection t).curvatureTensorNorm y| ≤
          4 * (K.flow.connection 0).scalarCurvature q) ∧
      ∀ a : ℝ, 0 < a → a ≤ 3 * r →
        ENNReal.ofReal ((ν / 27) * a ^ 3) ≤
          calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball q a) := by
  obtain ⟨q, s, hq, hs, hsr, hR, hscale, _, _, hbound⟩ :=
    m23_exists_backward_controlled_point_in_ball P K p x hr hx
  exact ⟨q, s, hq, hs, hsr, hR, hscale, hbound,
    m23_recentered_volume_lower_bound P K p q hr hν hq hvolume⟩

end PoincareConjecture
