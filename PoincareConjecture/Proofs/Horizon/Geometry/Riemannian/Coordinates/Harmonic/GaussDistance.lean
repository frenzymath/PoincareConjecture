import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.GaussNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.NormalRadial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.NormalRadius

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))

theorem edist_zero_eq_of_gauss
    (hgauss : ∀ x w, g.euclideanCoefficients x x w = inner ℝ x w)
    (x : EuclideanSpace ℝ (Fin n)) :
    g.edist 0 x = ENNReal.ofReal ‖x‖ := by
  let E := EuclideanSpace ℝ (Fin n)
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.refl E
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    simpa [e] using (contMDiff_id (I := 𝓡 n) (n := ∞)).contMDiffOn
  have he' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    simpa [e] using (contMDiff_id (I := 𝓡 n) (n := ∞)).contMDiffOn
  have hg : ∀ v ∈ e.source, ∀ w : E,
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w) = g.inner 0 v w := by
    intro v hv w
    simpa [e, euclideanCoefficients, OpenPartialHomeomorph.refl_apply] using!
      (hgauss v w).trans (g.euclideanCoefficients_zero_eq_of_gauss hgauss v w).symm
  have hn : g.tangentNorm 0 x = ‖x‖ := by
    change Real.sqrt (g.euclideanCoefficients 0 x x) = ‖x‖
    rw [g.euclideanCoefficients_zero_eq_of_gauss hgauss, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg x)]
  apply le_antisymm
  · simpa [e, hn, OpenPartialHomeomorph.refl_apply] using!
      g.edist_radial_le_of_gauss 0 e rfl he hg x (by intro t ht; trivial)
  · have hεbound (ε : ℝ) (hε : 0 < ε) :
        EDist.edist (Real.sqrt ε) (Real.sqrt (g.inner 0 x x + ε)) ≤ g.edist 0 x := by
      let f : E → ℝ := fun y => Real.sqrt (g.inner 0 y y + ε)
      have hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 1 f :=
        (contMDiff_iff_contDiff.mpr
          (g.contDiff_regularized_tangentNorm 0 hε)).of_le (by simp)
      have hbound : ∀ y v, |mvfderiv (𝓡 n) f y v| ≤
          (1 : ℝ≥0) * g.tangentNorm y v := by
        intro y v
        simpa [f, e, OpenPartialHomeomorph.refl_apply] using!
          g.regularized_tangentNorm_mfderiv_le 0 e he he' hg hε
            (show y ∈ e.target from Set.mem_univ _) v
      simpa [f] using g.edist_le_mul_edist_of_derivative_bound hf
        (by norm_num : (0 : ℝ≥0) < 1) hbound 0 x
    have ht : Tendsto (fun ε : ℝ => EDist.edist (Real.sqrt ε)
        (Real.sqrt (g.inner 0 x x + ε))) (𝓝[>] (0 : ℝ))
        (𝓝 (ENNReal.ofReal (g.tangentNorm 0 x))) := by
      have hc : Continuous (fun ε : ℝ => EDist.edist (Real.sqrt ε)
          (Real.sqrt (g.inner 0 x x + ε))) :=
        Real.continuous_sqrt.edist
          (Real.continuous_sqrt.comp (continuous_const.add continuous_id))
      simpa [edist_dist, Real.dist_eq, tangentNorm, abs_of_nonneg, Real.sqrt_nonneg]
        using hc.continuousAt.tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    rw [← hn]
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with ε hε using hεbound ε hε

theorem ball_zero_eq_of_gauss
    (hgauss : ∀ x w, g.euclideanCoefficients x x w = inner ℝ x w)
    (R : ℝ) : g.ball 0 R = Metric.ball 0 R := by
  ext x
  simp only [ball, Set.mem_ofPred_eq, g.edist_zero_eq_of_gauss hgauss,
    Metric.mem_ball, dist_zero_right]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)

end PoincareConjecture.RiemannianMetric
