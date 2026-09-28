import PoincareConjecture.Proofs.M47.CanonicalNeckScalarComparison
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckRestriction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47



theorem cap_affine_factor_bounds {beta gamma : ℝ}
    (hsmall : gamma ≤ 1 / 1200) (hbeta : |beta - 1| ≤ (16 / 5 : ℝ) * gamma) :
    0 < beta ∧ 0 < beta ^ (-1 / 2 : ℝ) ∧
      (99 / 100 : ℝ) ≤ beta ^ (-1 / 2 : ℝ) ∧
      beta ^ (-1 / 2 : ℝ) ≤ (101 / 100 : ℝ) ∧
      beta * (beta ^ (-1 / 2 : ℝ)) ^ 2 = 1 := by
  have hb := abs_le.mp hbeta
  have hlo : (374 / 375 : ℝ) ≤ beta := by linarith
  have hhi : beta ≤ (376 / 375 : ℝ) := by linarith
  have hpos : 0 < beta := by linarith
  have hlambda : 0 < beta ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hscale : beta * (beta ^ (-1 / 2 : ℝ)) ^ 2 = 1 := by
    rw [← Real.rpow_mul_natCast hpos.le (-1 / 2) 2]
    norm_num only [neg_div, neg_mul, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.rpow_neg_one]
    exact mul_inv_cancel₀ hpos.ne'
  have hlowsq : (374 / 375 : ℝ) * (beta ^ (-1 / 2 : ℝ)) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg (beta ^ (-1 / 2 : ℝ)))]
  have hhisq : 1 ≤ (376 / 375 : ℝ) * (beta ^ (-1 / 2 : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (sq_nonneg (beta ^ (-1 / 2 : ℝ)))]
  refine ⟨hpos, hlambda, ?_, ?_, hscale⟩ <;> nlinarith

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem cap_neck_normalized_scalar_difference (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200) (q : UnitTwoSphere)
    {c : ℝ} (hc : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    |N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c)) - 1| ≤
      (16 / 5 : ℝ) * N.epsilon := by
  have hQ : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have h := neck_pullback_scalar_difference_le N (by linarith only [hsmall]) g
    N.connection hQ (le_refl (0 : ℝ)) N.metric_comparison.close
    (N.coordinate_map (q, c)) (N.coordinate_map_mem_of_axial_mem hc)
  simpa only [sub_zero, div_one, inv_pow, div_inv_eq_mul, mul_comm] using h



theorem cap_neck_affine_factor_continuousOn (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200) (q : UnitTwoSphere) :
    ContinuousOn (fun c : ℝ =>
      (N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c))) ^ (-1 / 2 : ℝ))
      (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  have hcoord : ContinuousOn (fun c : ℝ => N.coordinate_map (q, c))
      (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    N.coordinate_map_smooth.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun c hc => ⟨mem_univ _, hc⟩)
  have hR := (M34.contMDiff_scalarCurvature N.connection).continuous.comp_continuousOn hcoord
  apply (continuousOn_const.mul hR).rpow_const
  intro c hc
  exact Or.inl (cap_affine_factor_bounds hsmall
    (cap_neck_normalized_scalar_difference N hsmall q hc)).1.ne'

end PoincareConjecture.M47
