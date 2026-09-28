import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.RadialSpeed
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Assembly
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Cutoff











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ENNReal Manifold ContDiff Topology

namespace Poincare.VolumeComparison

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]



theorem polarDensity_antitone_one
    (g : PoincareConjecture.RiemannianMetric 1 M) (p : M)
    {R : ℝ} {e : EuclideanSpace ℝ (Fin 1) → M}
    (he : ContMDiffOn (𝓡 1) (𝓡 1) ∞ e (Metric.ball 0 R))
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 1) (fun u : ℝ => e (u • v)) t 1) = ‖v‖)
    (hdist : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    AntitoneOn (fun t : ℝ =>
      (localMinimizingSet (fun v => g.edist p (e v)) R \
        terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R).indicator
        (fun v => ENNReal.ofReal (g.pullbackVolumeDensity e v))
        (t • (θ : EuclideanSpace ℝ (Fin 1)))) (Ioo 0 R) := by
  classical
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  have hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S := by
    intro v hv a ha0 ha1
    exact radial_minimizing_star g he hv (hspeed v hv.1) (hdist v hv.1) a ha0 ha1
  have hθ : ‖(θ : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  have hθ0 : (θ : EuclideanSpace ℝ (Fin 1)) ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at hθ
  have hdensity (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      g.pullbackVolumeDensity e (t • (θ : EuclideanSpace ℝ (Fin 1))) = 1 := by
    have htball : t • (θ : EuclideanSpace ℝ (Fin 1)) ∈ Metric.ball 0 R := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg ht.1.le, hθ, mul_one] using ht.2
    apply g.pullbackVolumeDensity_eq_one_of_radial_speed
      (smul_ne_zero ht.1.ne' hθ0)
    exact (g.tangentNorm_mfderiv_radial_eq
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds htball)).mdifferentiableAt (by simp))).trans
      (hspeed _ htball 1 (by simp))
  intro t ht s hs hts
  by_cases hsS : s • (θ : EuclideanSpace ℝ (Fin 1)) ∈ S \ T
  · have htS : t • (θ : EuclideanSpace ℝ (Fin 1)) ∈ S \ T := by
      have h := smul_mem_sdiff_terminalRadialPoints hstar hsS
        (div_pos ht.1 hs.1) ((div_le_one hs.1).mpr hts)
      simpa only [smul_smul, div_mul_cancel₀ _ hs.1.ne'] using h
    change (S \ T).indicator _ _ ≤ (S \ T).indicator _ _
    simp only [indicator_of_mem hsS, indicator_of_mem htS, hdensity s hs, hdensity t ht,
      le_refl]
  · change (S \ T).indicator _ _ ≤ (S \ T).indicator _ _
    simp only [indicator_of_notMem hsS, zero_le]

end Poincare.VolumeComparison
