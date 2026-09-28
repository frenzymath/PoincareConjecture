import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Myers.Segment
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.SegmentSpeed
import PoincareConjecture.Proofs.M34.Standard.CompactCompleteness

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47Positive

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

theorem exists_minimizing_segment_with_speed (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p x : M) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ gamma : ℝ → M,
      g.IsGeodesicOn gamma (Ioo (-epsilon) (1 + epsilon)) ∧
      gamma 0 = p ∧ gamma 1 = x ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (gamma s) (gamma t) = ENNReal.ofReal |s - t| * g.edist p x) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1) =
          (g.edist p x).toReal := by
  obtain ⟨epsilon, hepsilon, gamma, hgeo, hzero, hone, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p x
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-epsilon) (1 + epsilon) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have h0 := hI (show (0 : ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨C, hC⟩ := hgeo.exists_constant_tangentNorm (by linarith)
  have hv := (hgeo.hasDerivAt_chart_at h0 p (by
    simpa only [hzero] using mem_extChartAt_source p)).1
  have hC0 : g.tangentNorm p (deriv (fun t => extChartAt (𝓡 n) p (gamma t)) 0) = C := by
    simpa only [RiemannianMetric.chartCoefficients_self, RiemannianMetric.tangentNorm] using
      (hgeo.tangentNorm_initial h0 hzero hv).symm.trans (hC 0 h0)
  have hCd : (C : ℝ) = (g.edist p x).toReal := by
    have h := hgeo.initial_tangentNorm_eq_of_edist_segment hepsilon hzero hv hmin
    rw [hC0] at h
    simpa only [ENNReal.toReal_ofReal C.coe_nonneg] using congrArg ENNReal.toReal h
  exact ⟨epsilon, hepsilon, gamma, hgeo, hzero, hone, hmin,
    fun t ht => (hC t (hI ht)).trans hCd⟩

theorem exists_point_at_intrinsic_radius (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p x : M) {rho : ℝ} (hrho : 0 < rho)
    (hdistance : rho ≤ (g.edist p x).toReal) :
    ∃ y : M, (g.edist p y).toReal = rho := by
  let d := (g.edist p x).toReal
  have hd : 0 < d := hrho.trans_le hdistance
  obtain ⟨epsilon, hepsilon, gamma, hgeo, hzero, hone, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p x
  have hparameter : rho / d ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hrho.le hd.le, (div_le_one hd).mpr hdistance⟩
  refine ⟨gamma (rho / d), ?_⟩
  have h := congrArg ENNReal.toReal (hmin 0 (by simp) (rho / d) hparameter)
  rw [hzero, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    zero_sub, abs_neg, abs_of_nonneg hparameter.1] at h
  change (g.edist p (gamma (rho / d))).toReal = rho / d * d at h
  rwa [div_mul_cancel₀ _ hd.ne'] at h

theorem ricci_distance_sq_le_of_ball_lower (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (hc : MetricComplete g) (p x : M) {k : ℝ}
    (hRic : ∀ y : M, (g.edist p y).toReal ≤ (g.edist p x).toReal →
      ∀ v : TangentSpace (𝓡 n) y, k * g.inner y v v ≤ D.ricci y v v) :
    k * (g.edist p x).toReal ^ 2 ≤ 10 * (n : ℝ) := by
  let d := (g.edist p x).toReal
  by_cases hd : 0 < d
  · obtain ⟨epsilon, hepsilon, gamma, hgeo, hzero, hone, hmin, hspeed⟩ :=
      exists_minimizing_segment_with_speed g hc p x
    apply ConjugateFrame.ricci_mul_speed_sq_le_of_minimizing D hepsilon hgeo hd hspeed
    · rw [hzero, hone]
      exact (ENNReal.ofReal_toReal (g.edist_ne_top p x)).symm
    · intro t ht
      have hball : (g.edist p (gamma t)).toReal ≤ (g.edist p x).toReal := by
        have h := congrArg ENNReal.toReal (hmin 0 (by simp) t ht)
        rw [hzero, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
          zero_sub, abs_neg, abs_of_nonneg ht.1] at h
        rw [h]
        exact mul_le_of_le_one_left ENNReal.toReal_nonneg ht.2
      have hnonneg : 0 ≤ g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1) := by
        by_cases hz : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1 = 0
        · simp [hz]
        · exact (g.pos (gamma t) _ hz).le
      have hsq := congrArg (fun a : ℝ => a ^ 2) (hspeed t ht)
      rw [RiemannianMetric.tangentNorm, Real.sq_sqrt hnonneg] at hsq
      rw [← hsq]
      exact hRic (gamma t) hball _
  · have hz : d = 0 := le_antisymm (le_of_not_gt hd) ENNReal.toReal_nonneg
    change k * d ^ 2 ≤ _
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    positivity

end PoincareConjecture.M47Positive
