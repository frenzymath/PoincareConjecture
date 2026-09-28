import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem globalExponential_eq_radial_exponential
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) {R : ℝ}
    (hR : 0 < R)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M) (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) :
    g.globalExponential hc p (L v) = e v := by
  have hγ : g.IsGeodesicOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact hgeo v hv t ((convex_ball (0 : EuclideanSpace ℝ (Fin n)) R).smul_mem_of_zero_mem
      (by simpa using hR) hv ht)
  have hder : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hed' : HasFDerivAt (fun w => extChartAt (𝓡 n) p (e w))
      L.toContinuousLinearMap ((0 : ℝ) • v) := by simpa using hed
  have hvel := hed'.comp_hasDerivAt 0 hder
  simpa only [one_smul] using g.globalExponential_eq_endpoint hc p (L v) hγ
    (by simpa only [zero_smul] using he0) hvel

omit [T3Space M] in

theorem tangentNorm_orthonormal_frame (g : RiemannianMetric n M) (p : M)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (v : EuclideanSpace ℝ (Fin n)) : g.tangentNorm p (L v) = ‖v‖ := by
  have h := hL v v
  rw [g.chartCoefficients_self] at h
  simp only [tangentNorm, h, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]

theorem le_truncatedInjectivityRadius_of_radial_exponential
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) {R C r : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R) (hrC : r ≤ C)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hinj : InjOn e (Metric.ball 0 r)) :
    r ≤ g.truncatedInjectivityRadius hc C p := by
  apply g.le_truncatedInjectivityRadius hc p hr hrC
  intro v hv w hw heq
  have hnorm (z : EuclideanSpace ℝ (Fin n)) : g.tangentNorm p z = ‖L.symm z‖ := by
    simpa only [L.apply_symm_apply] using g.tangentNorm_orthonormal_frame p L hL (L.symm z)
  have hv' : L.symm v ∈ Metric.ball 0 r := by simpa only [mem_ofPred_eq, hnorm, Metric.mem_ball,
    dist_zero_right] using hv
  have hw' : L.symm w ∈ Metric.ball 0 r := by simpa only [mem_ofPred_eq, hnorm, Metric.mem_ball,
    dist_zero_right] using hw
  apply L.symm.injective
  apply hinj hv' hw'
  have hev := g.globalExponential_eq_radial_exponential hc p hR L e he0 hed hgeo
    (Metric.ball_subset_ball hrR hv')
  have hew := g.globalExponential_eq_radial_exponential hc p hR L e he0 hed hgeo
    (Metric.ball_subset_ball hrR hw')
  rw [L.apply_symm_apply] at hev hew
  exact hev.symm.trans (heq.trans hew)

theorem injOn_radial_exponential_of_le_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) {R C r : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hrR : r ≤ R)
    (hrρ : r ≤ g.truncatedInjectivityRadius hc C p)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R}) :
    InjOn e (Metric.ball 0 r) := by
  intro v hv w hw heq
  apply L.injective
  apply g.injOn_globalExponential_truncatedInjectivityRadius hc hC p
  · change g.tangentNorm p (L v) < g.truncatedInjectivityRadius hc C p
    rw [g.tangentNorm_orthonormal_frame p L hL]
    exact (show ‖v‖ < r by simpa using hv).trans_le hrρ
  · change g.tangentNorm p (L w) < g.truncatedInjectivityRadius hc C p
    rw [g.tangentNorm_orthonormal_frame p L hL]
    exact (show ‖w‖ < r by simpa using hw).trans_le hrρ
  · rw [g.globalExponential_eq_radial_exponential hc p hR L e he0 hed hgeo
      (Metric.ball_subset_ball hrR hv),
      g.globalExponential_eq_radial_exponential hc p hR L e he0 hed hgeo
      (Metric.ball_subset_ball hrR hw)]
    exact heq

end PoincareConjecture.RiemannianMetric
