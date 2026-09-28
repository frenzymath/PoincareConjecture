import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.MetricExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

namespace LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

lemma laplacian_coordinate_eq_neg_christoffel_trace (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    D.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y j) x =
      -(∑ i, CoordinateExponential.christoffelBilinear
        g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj i))) j := by
  have h := D.laplacian_eq_sum_fderiv_sub_christoffel
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt (n := ∞) (x := x))
  have hd : fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) j) =
      fun _ : EuclideanSpace ℝ (Fin n) => EuclideanSpace.proj j :=
    funext fun _ => ContinuousLinearMap.fderiv _
  rw [hd] at h
  simpa [RiemannianMetric.euclideanCoefficients] using! h

lemma laplacian_coordinate_eq_zero_of_coefficients (D : LeviCivitaData g)
    {B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (heq : g.euclideanCoefficients =ᶠ[𝓝 x] B)
    (htrace : (∑ i, CoordinateExponential.christoffelBilinear B x
      (EuclideanSpace.basisFun (Fin n) ℝ i) ((B x).inverse (EuclideanSpace.proj i))) = 0)
    (j : Fin n) :
    D.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y j) x = 0 := by
  have hΓ : CoordinateExponential.christoffelBilinear g.euclideanCoefficients x =
      CoordinateExponential.christoffelBilinear B x := by
    unfold CoordinateExponential.christoffelBilinear
    rw [heq.eq_of_nhds, heq.fderiv_eq]
  rw [D.laplacian_coordinate_eq_neg_christoffel_trace, hΓ, heq.eq_of_nhds, htrace]
  simp

end LeviCivitaData

namespace RiemannianMetric

lemma exists_harmonic_realization_on_ball
    {n : ℕ} {r R a b : ℝ} (hr : 0 < r) (hrR : r < R)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Metric.ball 0 R))
    (hsymm : ∀ x ∈ Metric.ball 0 R, ∀ v w, B x v w = B x w v)
    (hbound : ∀ x ∈ Metric.ball 0 R, ∀ v,
      a * ‖v‖ ^ 2 ≤ B x v v ∧ B x v v ≤ b * ‖v‖ ^ 2)
    (htrace : ∀ x ∈ Metric.ball 0 r,
      (∑ i, CoordinateExponential.christoffelBilinear B x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ((B x).inverse (EuclideanSpace.proj i))) = 0) :
    ∃ (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData h),
      (∀ x ∈ Metric.ball 0 r, h.euclideanCoefficients x = B x) ∧
      (∀ x v, a * ‖v‖ ^ 2 ≤ h.euclideanCoefficients x v v ∧
        h.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) ∧
      ∀ x ∈ Metric.ball 0 r, ∀ i : Fin n,
        D.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y i) x = 0 := by
  obtain ⟨h, heq, hbounds⟩ := exists_extension_on_ball hr hrR ha ha1 hb1 B hB hsymm hbound
  refine ⟨h, h.euclideanLeviCivitaData, heq, hbounds, ?_⟩
  intro x hx i
  apply h.euclideanLeviCivitaData.laplacian_coordinate_eq_zero_of_coefficients _ (htrace x hx) i
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  exact heq y hy

end RiemannianMetric
end PoincareConjecture
