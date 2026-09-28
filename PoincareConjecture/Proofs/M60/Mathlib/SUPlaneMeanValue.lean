import PoincareConjecture.Proofs.M60.Mathlib.SUSubsolutionMeanValue
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Euclidean
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.M60

def suPlaneLaplacian (u : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin 2) ℝ i)
    (EuclideanSpace.basisFun (Fin 2) ℝ i)

theorem suPlaneLaplacian_add_left (u : EuclideanSpace ℝ (Fin 2) → ℝ)
    (p x : EuclideanSpace ℝ (Fin 2)) :
    suPlaneLaplacian (fun y => u (p + y)) x = suPlaneLaplacian u (p + x) := by
  have hd : fderiv ℝ (fun y => u (p + y)) = fun y => fderiv ℝ u (p + y) :=
    funext fun _ => fderiv_comp_add_left p
  simp only [suPlaneLaplacian, hd, fderiv_comp_add_left]

theorem suSetIntegral_closedBall_add_left (u : EuclideanSpace ℝ (Fin 2) → ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    (∫ x in Metric.closedBall 0 r, u (p + x)) =
      ∫ x in Metric.closedBall p r, u x := by
  have heq : (fun x => p + x) ⁻¹' Metric.closedBall p r = Metric.closedBall 0 r := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      add_sub_cancel_left, sub_zero]
  have h := (measurePreserving_add_left
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) p).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft p).measurableEmbedding u (Metric.closedBall p r)
  rw [heq] at h
  exact h

theorem exists_plane_mean_value_sq :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : EuclideanSpace ℝ (Fin 2) → ℝ),
      ContDiff ℝ ∞ u → (∀ x, 0 < u x) →
      ∀ (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r → r ≤ 1 →
        (∀ x ∈ Metric.ball p r, -(1 / r ^ 2) * u x ≤ suPlaneLaplacian u x) →
        r ^ 2 * (u p) ^ 2 ≤ C ^ 2 *
          ∫ x in Metric.closedBall p (r / 2), (u x) ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := exists_plane_subsolution_mean_value
    (a := 1) (b := 1) (Λ := 1) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun u hu hpos p r hr hr1 hlap => ?_⟩
  let v : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => u (p + x)
  have hv : ContDiff ℝ ∞ v := hu.comp (contDiff_const.add contDiff_id)
  let g := RiemannianMetric.euclideanMetric 2
  let D := g.euclideanLeviCivitaData
  have hell (x : EuclideanSpace ℝ (Fin 2)) (_hx : x ∈ Metric.ball 0 r)
      (w : EuclideanSpace ℝ (Fin 2)) :
      1 * ‖w‖ ^ 2 ≤ g.euclideanCoefficients x w w ∧
        g.euclideanCoefficients x w w ≤ 1 * ‖w‖ ^ 2 := by
    change 1 * ‖w‖ ^ 2 ≤ inner ℝ w w ∧ inner ℝ w w ≤ 1 * ‖w‖ ^ 2
    simp only [one_mul, real_inner_self_eq_norm_sq, le_refl, and_self]
  have hlapv (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Metric.ball 0 r) :
      -(1 / r ^ 2) * v x ≤ D.laplacian v x := by
    rw [D.laplacian_euclideanMetric hv.contDiffAt]
    change -(1 / r ^ 2) * v x ≤ suPlaneLaplacian v x
    rw [suPlaneLaplacian_add_left]
    exact hlap (p + x) (by
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx)
  have hm := hmean r hr hr1 g D hell v hv (fun x => hpos (p + x)) hlapv
  have hm' : u p ≤ (C / r) *
      (eLpNorm v 2 (volume.restrict (Metric.closedBall 0 (r / 2)))).toReal := by
    simpa only [v, add_zero] using hm
  have hs := mul_self_le_mul_self (hpos p).le hm'
  rw [← pow_two, ← pow_two, mul_pow, div_pow,
    Poincare.Analysis.Sobolev.eLpNorm_toReal_sq_eq_integral
      (HarmonicCoordinates.continuous_memLp_restrict_closedBall hv.continuous 0 (r / 2) 2)] at hs
  have hi : (∫ x in Metric.closedBall 0 (r / 2), (v x) ^ 2) =
      ∫ x in Metric.closedBall p (r / 2), (u x) ^ 2 :=
    suSetIntegral_closedBall_add_left (fun x => (u x) ^ 2) p (r / 2)
  rw [hi] at hs
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg r)
  convert! hmul using 1
  field_simp

end PoincareConjecture.M60
