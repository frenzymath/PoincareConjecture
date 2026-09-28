import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.NoBranching
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.CutTime

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace Poincare.VolumeComparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem injOn_localMinimizingSet_sdiff_terminal
    (g : PoincareConjecture.RiemannianMetric n M) (p : M) {R : ℝ}
    {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
      L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hspeed : ∀ v ∈ Metric.ball 0 R,
      g.tangentNorm (e ((0 : ℝ) • v))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t : ℝ => e (t • v)) 0 1) = ‖v‖) :
    InjOn e (localMinimizingSet (fun v => g.edist p (e v)) R \
      terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R) := by
  intro v hv w hw heq
  have hnorm : ‖v‖ = ‖w‖ := by
    have hh := hv.1.2.symm.trans ((congrArg (g.edist p) heq).trans hw.1.2)
    have hreal := congrArg ENNReal.toReal hh
    simpa only [ENNReal.toReal_ofReal (norm_nonneg v),
      ENNReal.toReal_ofReal (norm_nonneg w)] using hreal
  by_cases hv0 : v = 0
  · have hw0 : w = 0 := norm_eq_zero.mp (by simpa only [hv0, norm_zero] using hnorm.symm)
    exact hv0.trans hw0.symm
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  obtain ⟨q, hq, hqR, hqS⟩ : ∃ q : ℚ, 1 < (q : ℝ) ∧ (q : ℝ) * ‖v‖ < R ∧
      (q : ℝ) • v ∈ localMinimizingSet (fun z => g.edist p (e z)) R := by
    by_contra h
    apply hv.2
    refine ⟨hv.1, hv0, mem_iInter.mpr ?_⟩
    intro q hq
    exact h ⟨q, hq⟩
  have hseg {z : EuclideanSpace ℝ (Fin n)} {b : ℝ} (hb : b * ‖z‖ < R)
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b) : t • z ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)).trans_lt hb
  have hγ : g.IsGeodesicOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) (q : ℝ)) :=
    fun t ht => hgeo v hv.1.1 t (hseg hqR ht)
  have hwR : (1 : ℝ) * ‖w‖ < R := by
    simpa only [one_mul, Metric.mem_ball, dist_zero_right] using hw.1.1
  have hη : g.IsGeodesicOn (fun t : ℝ => e (t • w)) (Icc (0 : ℝ) 1) :=
    fun t ht => hgeo w hw.1.1 t (hseg hwR ht)
  have hγspeed : ∀ t ∈ Icc (0 : ℝ) (q : ℝ),
      g.tangentNorm (e (t • v))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t : ℝ => e (t • v)) t 1) = ‖v‖ := by
    intro t ht
    have h := tangentNorm_eq_of_mem_Icc g hγ ht (show (0 : ℝ) ∈ Icc 0 (q : ℝ) by
      constructor <;> linarith)
    exact h.trans (hspeed v hv.1.1)
  have hηspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • w))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t : ℝ => e (t • w)) t 1) = ‖v‖ := by
    intro t ht
    have h := tangentNorm_eq_of_mem_Icc g hη ht (by simp : (0 : ℝ) ∈ Icc 0 1)
    exact h.trans ((hspeed w hw.1.1).trans hnorm.symm)
  have hdist : g.edist (e ((0 : ℝ) • v)) (e ((q : ℝ) • v)) =
      ENNReal.ofReal ((q : ℝ) * ‖v‖) := by
    simpa only [mem_ofPred_eq, zero_smul, he0, norm_smul,
      Real.norm_of_nonneg (by linarith : 0 ≤ (q : ℝ))]
      using hqS.2
  have hnear := eq_nhds_of_minimizing_extension g hq hpos hγ hη
    (by simp) (by simpa only [one_smul] using heq) hγspeed hηspeed hdist
    0 (by simp)
  have hderiv (z : EuclideanSpace ℝ (Fin n)) :
      HasDerivAt (fun t : ℝ => extChartAt (𝓡 n) p (e (t • z))) (L z) 0 := by
    have hdline : HasDerivAt (fun t : ℝ => t • z) z 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe] using
      hed.comp_hasDerivAt_of_eq 0 hdline (by simp)
  apply L.injective
  have hd := (hnear.fun_comp (extChartAt (𝓡 n) p)).deriv_eq
  change deriv (fun t : ℝ => extChartAt (𝓡 n) p (e (t • v))) 0 =
    deriv (fun t : ℝ => extChartAt (𝓡 n) p (e (t • w))) 0 at hd
  simpa only [(hderiv v).deriv, (hderiv w).deriv] using hd

end Poincare.VolumeComparison
