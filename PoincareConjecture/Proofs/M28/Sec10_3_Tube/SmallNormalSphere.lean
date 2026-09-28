import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.NormalBall
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Orthonormal










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]





theorem exists_three_points_at_small_edist
    (g : RiemannianMetric 3 M) (p : M) {R : ℝ} (hR : 0 < R) :
    ∃ delta : ℝ, 0 < delta ∧ delta < R ∧ ∃ z : Fin 3 → M,
      Function.Injective z ∧ ∀ i, g.edist p (z i) = ENNReal.ofReal delta := by
  let E := EuclideanSpace ℝ (Fin 3)
  obtain ⟨e, h0, he0, he, he', hgauss, _hball, _hflow⟩ :=
    g.exists_exponential_chart_gauss p
  obtain ⟨rho, hrho, hsource, hdist⟩ :=
    g.exists_tangentBall_edist_eq_of_gauss p e h0 he0 he he' hgauss
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  have hLinner (v w : E) : g.inner p (L v) (L w) = inner ℝ v w := by
    rw [← g.chartCoefficients_center]
    exact hL v w
  have hLnorm (v : E) : g.tangentNorm p (L v) = ‖v‖ := by
    rw [RiemannianMetric.tangentNorm, hLinner, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg v)]
  let delta := min rho R / 2
  have hdelta : 0 < delta := half_pos (lt_min hrho hR)
  have hdeltarho : delta < rho :=
    (half_lt_self (lt_min hrho hR)).trans_le (min_le_left _ _)
  have hdeltaR : delta < R :=
    (half_lt_self (lt_min hrho hR)).trans_le (min_le_right _ _)
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let v : Fin 3 → E := fun i => L (delta • b i)
  have hvnorm (i : Fin 3) : g.tangentNorm p (v i) = delta := by
    change g.tangentNorm p (L (delta • b i)) = delta
    rw [hLnorm, norm_smul, Real.norm_eq_abs, abs_of_pos hdelta,
      b.norm_eq_one i, mul_one]
  have hvsource (i : Fin 3) : v i ∈ e.source := by
    apply hsource
    change g.tangentNorm p (v i) < rho
    rw [hvnorm]
    exact hdeltarho
  let z : Fin 3 → M := fun i => e (v i)
  refine ⟨delta, hdelta, hdeltaR, z, ?_, ?_⟩
  · intro i j hij
    have hv : v i = v j := e.injOn (hvsource i) (hvsource j) hij
    have hscaled : delta • b i = delta • b j := L.injective hv
    exact b.toBasis.injective (smul_right_injective E hdelta.ne' hscaled)
  · intro i
    change g.edist p (e (v i)) = ENNReal.ofReal delta
    rw [hdist (v i) (by rw [hvnorm]; exact hdeltarho), hvnorm]

end PoincareConjecture.RiemannianMetric
