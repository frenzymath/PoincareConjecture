import PoincareConjecture.Proofs.M47.CanonicalNeckConnectionBounds
import PoincareConjecture.Proofs.M47.BlowupControlsCapRicciFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

open PoincareConjecture.Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem abs_four_terms (a b c d : ℝ) :
    |a - b + c - d| ≤ |a| + |b| + |c| + |d| := by
  have hsub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  linarith only [hsub (a - b + c) d, abs_add_le (a - b) c, hsub a b]

theorem terminalCurvature_numerical_curvature_component
    {g0 g1 : RiemannianMetric 3 E} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (x : E) (e : E ≃L[ℝ] E)
    (he : ∀ v w : E, g0.inner x (e v) (e w) = inner ℝ v w)
    (hzero : ∀ u v : E, D0.euclideanConnection u v x = 0)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 2)
    (hbound0 : g0.tensorNorm (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ gamma)
    (hbound1 : g0.tensorNorm (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1))) x ≤ gamma)
    (hbound2 : g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)))) x ≤ gamma)
    (i j k l : Fin 3) :
    |inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ l) (e.symm
      (D1.curvature x (e (EuclideanSpace.basisFun (Fin 3) ℝ i))
          (e (EuclideanSpace.basisFun (Fin 3) ℝ j)) (e (EuclideanSpace.basisFun (Fin 3) ℝ k)) -
        D0.curvature x (e (EuclideanSpace.basisFun (Fin 3) ℝ i))
          (e (EuclideanSpace.basisFun (Fin 3) ℝ j)) (e (EuclideanSpace.basisFun (Fin 3) ℝ k))))| ≤
      18 * gamma + 810 * gamma ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let Delta := fun u v y => D1.euclideanConnection u v y - D0.euclideanConnection u v y
  let B := fun a c d => inner ℝ (b a) (e.symm (Delta (e (b c)) (e (b d)) x))
  let dB := fun a c d r =>
    inner ℝ (b a) (e.symm (fderiv ℝ (Delta (e (b c)) (e (b d))) x (e (b r))))
  have hB (a c d : Fin 3) : |B a c d| ≤ 9 * gamma :=
    neck_connection_coefficient_bound D0 D1 x e he hgamma hsmall hbound0 hbound1 a c d
  have hdB (a c d r : Fin 3) : |dB a c d r| ≤ 9 * gamma + 162 * gamma ^ 2 :=
    neck_connection_derivative_coefficient_bound D0 D1 x e he hzero hgamma hsmall
      hbound0 hbound1 hbound2 a c d r
  have hsum (a c d r : Fin 3) : |∑ m : Fin 3, B a c m * B m d r| ≤ 243 * gamma ^ 2 := by
    calc
      _ ≤ ∑ m : Fin 3, |B a c m * B m d r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m : Fin 3, (9 * gamma) * (9 * gamma) := by
        apply Finset.sum_le_sum
        intro m _
        rw [abs_mul]
        exact mul_le_mul (hB a c m) (hB m d r) (abs_nonneg _) (by positivity)
      _ = _ := by simp; ring
  rw [cap_curvature_difference_normal D0 D1 x hzero]
  have hlinear (v1 v2 v3 v4 : E) :
      inner ℝ (b l) (e.symm (v1 - v2 + v3 - v4)) =
        inner ℝ (b l) (e.symm v1) - inner ℝ (b l) (e.symm v2) +
          inner ℝ (b l) (e.symm v3) - inner ℝ (b l) (e.symm v4) := by
    simp only [map_sub, map_add, inner_sub_right, inner_add_right]
  rw [hlinear]
  rw [cap_connectionDifference_compose_frame D0 D1 e x,
    cap_connectionDifference_compose_frame D0 D1 e x]
  change |dB l j k i - dB l i k j +
      (∑ m : Fin 3, B l i m * B m j k) - (∑ m : Fin 3, B l j m * B m i k)| ≤ _
  calc
    _ ≤ |dB l j k i| + |dB l i k j| +
        |∑ m : Fin 3, B l i m * B m j k| + |∑ m : Fin 3, B l j m * B m i k| :=
      abs_four_terms _ _ _ _
    _ ≤ (9 * gamma + 162 * gamma ^ 2) + (9 * gamma + 162 * gamma ^ 2) +
        243 * gamma ^ 2 + 243 * gamma ^ 2 := by
      exact add_le_add (add_le_add (add_le_add (hdB l j k i) (hdB l i k j))
        (hsum l i j k)) (hsum l j i k)
    _ = _ := by ring

end PoincareConjecture.M47
