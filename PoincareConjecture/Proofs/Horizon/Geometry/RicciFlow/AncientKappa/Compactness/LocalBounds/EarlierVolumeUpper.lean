import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Model
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem m23_earlier_ball_volume_le_exp_mul_terminal_ball
    (P : M23NormalizedKappaCompactnessPredecessors) (K : AncientKappaSolution 3 M)
    (p : M) {δ B r : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ t ∈ Icc (-δ) 0, ∀ x ∈ (K.flow.metric 0).ball p r,
      (K.flow.connection t).curvatureTensorNorm x ≤ B) :
    calibratedMetricVolume (K.flow.metric (-δ)) ((K.flow.metric (-δ)).ball p r) ≤
      ENNReal.ofReal (Real.exp (27 * B * δ)) ^ 3 *
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r) := by
  let U := (K.flow.metric 0).ball p r
  let c := Real.exp (27 * B * δ)
  have hc : 0 < c := Real.exp_pos _
  have hzero : (0 : ℝ) ∈ Icc (-δ) 0 := ⟨by linarith, le_rfl⟩
  have hearly : -δ ∈ Icc (-δ) 0 := ⟨le_rfl, neg_nonpos.mpr hδ⟩
  have hRic (t : ℝ) (ht : t ∈ Icc (-δ) 0) (x : M) (hx : x ∈ U)
      (v : TangentSpace (𝓡 3) x) :
      |(K.flow.connection t).ricci x v v| ≤ (27 * B) * (K.flow.metric t).inner x v v := by
    have h := (K.flow.connection t).abs_ricci_quadratic_le_curvatureTensorNorm x v
    have hv : 0 ≤ (K.flow.metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((K.flow.metric t).pos x v hv).le
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at h
    norm_num at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound t ht x hx) (by norm_num)) hv)
  have hbackward (x : M) (hx : x ∈ U) (v : TangentSpace (𝓡 3) x) :
      (K.flow.metric (-δ)).tangentNorm x v ≤ c * (K.flow.metric 0).tangentNorm x v := by
    simpa only [sub_zero, abs_neg, abs_of_nonneg hδ] using
      K.flow.tangentNorm_le_exp_of_ricci_bound (convex_Icc (-δ) 0) (fun _ ht => ht.2)
        x v (27 * B) (fun t ht => hRic t ht x hx v) hzero hearly
  have hU : IsOpen U := by
    let := (K.flow.metric 0).toMetricSpace
    rw [show U = Metric.ball p r from ((K.flow.metric 0).toMetricSpace_ball p r).symm]
    exact Metric.isOpen_ball
  have hvol := (K.flow.metric 0).volumeMeasure_image_le_of_tangentNorm_le
    (K.flow.metric (-δ)) (OpenPartialHomeomorph.refl M) hU (subset_univ U)
    contMDiffOn_id hc (by
      intro x hx v
      change (K.flow.metric (-δ)).tangentNorm x (mfderiv (𝓡 3) (𝓡 3) id x v) ≤ _
      rw [mfderiv_id]
      exact hbackward x hx v)
    hU.measurableSet (Subset.refl U)
  change (K.flow.metric (-δ)).volumeMeasure (id '' U) ≤ _ at hvol
  rw [image_id] at hvol
  rw [calibratedMetricVolume_eq_volumeMeasure, calibratedMetricVolume_eq_volumeMeasure]
  exact (measure_mono (P.ball_monotone M K (-δ) 0 (neg_nonpos.mpr hδ) le_rfl p r)).trans hvol

private theorem exists_small_time_volume_inflation {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ Real.exp (27 * B * δ) ^ 3 ≤ 3 / 2 := by
  have hlog : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  let δ : ℝ := min (1 / 2) (Real.log (3 / 2) / (81 * (B + 1)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hproduct : δ * (81 * (B + 1)) ≤ Real.log (3 / 2) :=
    (le_div_iff₀ (by positivity : 0 < 81 * (B + 1))).mp (min_le_right _ _)
  have hexponent : 81 * B * δ ≤ Real.log (3 / 2) := by nlinarith
  refine ⟨δ, hδ, hδ1, ?_⟩
  calc
    Real.exp (27 * B * δ) ^ 3 = Real.exp (81 * B * δ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr hexponent
    _ = 3 / 2 := Real.exp_log (by norm_num)

namespace AncientKappaSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance earlierVolumeCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (K : ∀ k, AncientKappaSolution 3 (C k).carrier) (p : ∀ k, (C k).carrier)

theorem exists_earlier_unit_ball_volume_upper_bound
    (P : M23NormalizedKappaCompactnessPredecessors) {B ν : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (p k) 1,
      |((K k).flow.connection t).curvatureTensorNorm x| ≤ B)
    (hvolume : ∀ k, calibratedMetricVolume ((K k).flow.metric 0)
      (((K k).flow.metric 0).ball (p k) 1) ≤ ENNReal.ofReal ν) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ k,
      calibratedMetricVolume ((K k).flow.metric (-δ))
        (((K k).flow.metric (-δ)).ball (p k) 1) ≤ ENNReal.ofReal ((3 / 2) * ν) := by
  obtain ⟨δ, hδ, hδ1, hfactor⟩ := exists_small_time_volume_inflation hB
  refine ⟨δ, hδ, hδ1, fun k => ?_⟩
  have htransfer := m23_earlier_ball_volume_le_exp_mul_terminal_ball P (K k) (p k) hδ.le
    (r := 1) (B := B) (fun t ht x hx => (le_abs_self _).trans (hbound k t ht.2 x hx))
  have hfactor' : ENNReal.ofReal (Real.exp (27 * B * δ)) ^ 3 ≤ ENNReal.ofReal (3 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hfactor
  apply htransfer.trans
  calc
    _ ≤ ENNReal.ofReal (3 / 2 : ℝ) * ENNReal.ofReal ν := mul_le_mul' hfactor' (hvolume k)
    _ = ENNReal.ofReal ((3 / 2) * ν) := (ENNReal.ofReal_mul (by norm_num)).symm

theorem exists_earlier_half_euclidean_unit_ball_volume_bound
    (P : M23NormalizedKappaCompactnessPredecessors) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (p k) 1,
      |((K k).flow.connection t).curvatureTensorNorm x| ≤ B)
    (hvolume : ∀ k, calibratedMetricVolume ((K k).flow.metric 0)
      (((K k).flow.metric 0).ball (p k) 1) =
        ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 3 / 2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ k,
      calibratedMetricVolume ((K k).flow.metric (-δ))
        (((K k).flow.metric (-δ)).ball (p k) 1) ≤
          ENNReal.ofReal ((3 / 4) * RiemannianMetric.euclideanUnitBallVolume 3) := by
  obtain ⟨δ, hδ, hδ1, hvol⟩ := exists_earlier_unit_ball_volume_upper_bound
    C K p P hB hbound (fun k => (hvolume k).le)
  refine ⟨δ, hδ, hδ1, fun k => ?_⟩
  convert hvol k using 1
  congr 1
  ring

end AncientKappaSequence
end PoincareConjecture
