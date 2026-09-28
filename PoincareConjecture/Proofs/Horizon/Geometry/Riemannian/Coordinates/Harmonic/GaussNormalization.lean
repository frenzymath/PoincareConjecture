import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Euclidean

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))

theorem euclideanCoefficients_zero_eq_of_gauss
    (hgauss : ∀ x w, g.euclideanCoefficients x x w = inner ℝ x w)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.euclideanCoefficients 0 v w = inner ℝ v w := by
  have hc : ContinuousAt (fun t : ℝ => g.euclideanCoefficients (t • v) v w) 0 := by
    apply ContinuousAt.clm_apply _ continuousAt_const
    apply ContinuousAt.clm_apply _ continuousAt_const
    exact (g.contDiffAt_euclideanCoefficients 0).continuousAt.comp_of_eq
      (show ContinuousAt (fun t : ℝ => t • v) 0 by fun_prop) (zero_smul ℝ v)
  have ht : Tendsto (fun t : ℝ => g.euclideanCoefficients (t • v) v w)
      (𝓝[>] (0 : ℝ)) (𝓝 (g.euclideanCoefficients 0 v w)) := by
    simpa using hc.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hh := hgauss (t • v) w
  simp only [map_smul, smul_apply, smul_eq_mul, real_inner_smul_left] at hh
  exact ((mul_left_cancel₀ (ne_of_gt ht)) hh).symm

end PoincareConjecture.RiemannianMetric
