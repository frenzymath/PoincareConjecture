import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff.DistanceApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

theorem exists_smooth_weight_separating_balls (D : LeviCivitaData g)
    (x y : M) {r ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) :
    ∃ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ ∧
      (∀ z, g.tangentNorm z (D.gradient ψ z) ≤ 2 * a) ∧
      (∀ z ∈ g.ball x r, ψ z ≤ a * (r + ε)) ∧
      (∀ z ∈ g.ball y r, a * ((g.edist x y).toReal - r - ε) ≤ ψ z) := by
  obtain ⟨u, hu, he, hd⟩ := g.exists_smooth_distance_approx_with_error x hε
  refine ⟨fun z => a * u z, contMDiff_const.mul hu, ?_, ?_, ?_⟩
  · intro z
    apply (D.gradient_norm_le_iff _ z (mul_nonneg (by norm_num) ha)).mpr
    intro v
    rw [mvfderiv_const_mul, abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (hd z v) ha).trans_eq (by ring)
  · intro z hz
    have hzr : (g.edist x z).toReal < r :=
      (ENNReal.toReal_lt_of_lt_ofReal hz)
    have hez := (abs_le.mp (he z)).2
    exact mul_le_mul_of_nonneg_left (by linarith) ha
  · intro z hz
    have hzr : (g.edist y z).toReal < r :=
      ENNReal.toReal_lt_of_lt_ofReal hz
    have hdist := g.abs_toReal_edist_sub_le x y z
    have hez := (abs_le.mp (he z)).1
    exact mul_le_mul_of_nonneg_left (by
      have := (abs_le.mp hdist).2
      linarith) ha

end PoincareConjecture.LeviCivitaData
