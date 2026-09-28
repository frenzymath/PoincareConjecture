import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.CutTime
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialCurve
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentSpeed












noncomputable section
set_option autoImplicit false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

namespace Poincare.VolumeComparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem image_localMinimizingSet_eq_ball
    (g : PoincareConjecture.RiemannianMetric n M) (p : M) {R : ℝ}
    (hR : 0 < R) (hcompact : IsCompact (closure (g.ball p R)))
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
      L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R}) :
    e '' localMinimizingSet (fun v => g.edist p (e v)) R = g.ball p R := by
  apply Set.Subset.antisymm
  · rintro q ⟨v, hv, rfl⟩
    change g.edist p (e v) < ENNReal.ofReal R
    have hvdist : g.edist p (e v) = ENNReal.ofReal ‖v‖ := hv.2
    rw [hvdist]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr
      (by simpa only [Metric.mem_ball, dist_zero_right] using hv.1)
  · intro q hq
    obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
      g.exists_minimizing_geodesic_of_precompact_ball p q hR hcompact hq
    let c := extChartAt (𝓡 n) p
    let w := deriv (fun t => c (γ t)) 0
    let v := L.symm w
    have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
    have hγw : HasDerivAt (fun t => c (γ t)) w 0 :=
      (hγ.hasDerivAt_chart_at h0 p
        (by simpa only [hγ0] using mem_extChartAt_source p)).1
    have hspeed : ENNReal.ofReal (g.tangentNorm p w) = g.edist p q :=
      hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hγw hmin
    have hLv : L v = w := L.apply_symm_apply w
    have hnorm : g.tangentNorm p w = ‖v‖ := by
      rw [← hLv]
      unfold PoincareConjecture.RiemannianMetric.tangentNorm
      rw [← g.chartCoefficients_self p (L v) (L v), hL,
        real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]
    rw [hnorm] at hspeed
    have hv : v ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mp (hspeed.trans_lt hq)
    have hη : g.IsGeodesicOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1) := by
      intro t ht
      apply hgeo v hv t
      change t • v ∈ Metric.ball 0 R
      rw [Metric.mem_ball, dist_zero_right] at hv ⊢
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt (by simpa using hv)
    have hηw : HasDerivAt (fun t : ℝ => c (e (t • v))) w 0 := by
      have hdline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
      have hcomp := hed.comp_hasDerivAt_of_eq 0 hdline (by simp)
      simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, hLv] using hcomp
    have hγ' : g.IsGeodesicOn γ (Icc (0 : ℝ) 1) := by
      intro t ht
      exact hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have heq : e v = q := by
      have hh := PoincareConjecture.RiemannianMetric.geodesic_endpoint_eq_of_initial_data
        hγ' hη hγ0 (by simpa using he0) hγw hηw
      simpa only [one_smul, hγ1] using hh.symm
    refine ⟨v, ⟨hv, ?_⟩, heq⟩
    change g.edist p (e v) = ENNReal.ofReal ‖v‖
    simpa only [heq] using hspeed.symm

omit [T2Space M] in


theorem image_localMinimizingSet_inter_ball
    (g : PoincareConjecture.RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R r : ℝ}
    (hcover : e '' localMinimizingSet (fun v => g.edist p (e v)) R = g.ball p R)
    (hr : 0 < r) (hrR : r ≤ R) :
    e '' (localMinimizingSet (fun v => g.edist p (e v)) R ∩ Metric.ball 0 r) =
      g.ball p r := by
  apply Set.Subset.antisymm
  · rintro q ⟨v, ⟨hv, hvr⟩, rfl⟩
    have hvdist : g.edist p (e v) = ENNReal.ofReal ‖v‖ := hv.2
    change g.edist p (e v) < ENNReal.ofReal r
    rw [hvdist]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr
      (by simpa only [Metric.mem_ball, dist_zero_right] using hvr)
  · intro q hq
    have hqR : q ∈ g.ball p R := hq.trans_le (ENNReal.ofReal_le_ofReal hrR)
    rw [← hcover] at hqR
    obtain ⟨v, hv, rfl⟩ := hqR
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    have hvdist : g.edist p (e v) = ENNReal.ofReal ‖v‖ := hv.2
    change g.edist p (e v) < ENNReal.ofReal r at hq
    rw [hvdist] at hq
    simpa only [Metric.mem_ball, dist_zero_right] using
      (ENNReal.ofReal_lt_ofReal_iff hr).mp hq

end Poincare.VolumeComparison
