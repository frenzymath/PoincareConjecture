import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Nonsingular
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.CutSet





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem isInvertible_mfderiv_on_nonterminal
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {p : M} {R : ℝ}
    {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R)) (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖) :
    ∀ v ∈ Poincare.VolumeComparison.localMinimizingSet (fun w => g.edist p (e w)) R \
      Poincare.VolumeComparison.terminalRadialPoints
        (Poincare.VolumeComparison.localMinimizingSet (fun w => g.edist p (e w)) R) R,
      (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
  apply Poincare.VolumeComparison.Conjugate.isInvertible_on_nonterminal_of_extension g p
  intro v hv h
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg v)
    (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  have hinit := isInvertible_mfderiv_zero_of_chart_derivative
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hR))).mdifferentiableAt
      (by simp)) he0 hed
  rcases h with hzero | ⟨hne, q, hq, hqR, hmin⟩
  · subst v
    exact hinit
  · exact g.isInvertible_mfderiv_of_minimizing_extension D he he0 hinit hgeo hspeed
      hv hne hq hqR hmin

end PoincareConjecture.RiemannianMetric
