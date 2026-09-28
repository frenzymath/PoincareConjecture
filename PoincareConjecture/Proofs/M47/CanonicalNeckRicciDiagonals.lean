import PoincareConjecture.Proofs.M47.CanonicalNeckConnectionBounds
import PoincareConjecture.Proofs.M47.BlowupControlsCapRicciFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem abs_difference_le (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

theorem neck_ricci_diagonal_error_bound {g0 g1 : RiemannianMetric 3 E}
    (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1) (x : E) (e : E ≃L[ℝ] E)
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
    (i : Fin 3) :
    |D1.ricci x (e (EuclideanSpace.basisFun (Fin 3) ℝ i))
        (e (EuclideanSpace.basisFun (Fin 3) ℝ i)) -
      D0.ricci x (e (EuclideanSpace.basisFun (Fin 3) ℝ i))
        (e (EuclideanSpace.basisFun (Fin 3) ℝ i))| ≤ 54 * gamma + 2430 * gamma ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let Delta := fun u v y => D1.euclideanConnection u v y - D0.euclideanConnection u v y
  let B := fun k i j => inner ℝ (b k) (e.symm (Delta (e (b i)) (e (b j)) x))
  let dB := fun l k i j =>
    inner ℝ (b k) (e.symm (fderiv ℝ (Delta (e (b i)) (e (b j))) x (e (b l))))
  let D := 9 * gamma + 162 * gamma ^ 2
  have hB (a c d : Fin 3) : |B a c d| ≤ 9 * gamma :=
    neck_connection_coefficient_bound D0 D1 x e he hgamma hsmall hbound0 hbound1 a c d
  have hdB (a c d f : Fin 3) : |dB a c d f| ≤ D :=
    neck_connection_derivative_coefficient_bound D0 D1 x e he hzero hgamma hsmall
      hbound0 hbound1 hbound2 c d f a
  have hproduct (a c d f h j : Fin 3) :
      |B a c d * B f h j| ≤ (9 * gamma) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hB a c d) (hB f h j) (abs_nonneg _) (by positivity)
  have hquad (k l : Fin 3) :
      |B k k l * B l i i - B k i l * B l k i| ≤ 2 * (9 * gamma) ^ 2 := by
    apply (abs_difference_le _ _).trans
    linarith only [hproduct k k l l i i, hproduct k i l l k i]
  have hsum (k : Fin 3) :
      |∑ l : Fin 3, (B k k l * B l i i - B k i l * B l k i)| ≤
        3 * (2 * (9 * gamma) ^ 2) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _l : Fin 3, 2 * (9 * gamma) ^ 2 :=
        Finset.sum_le_sum fun l _ => hquad k l
      _ = _ := by simp
  have hrow (k : Fin 3) :
      |(dB k k i i - dB i k k i) +
        ∑ l : Fin 3, (B k k l * B l i i - B k i l * B l k i)| ≤
          2 * D + 3 * (2 * (9 * gamma) ^ 2) := by
    apply (abs_add_le _ _).trans
    have hderivative := (abs_difference_le (dB k k i i) (dB i k k i)).trans
      (add_le_add (hdB k k i i) (hdB i k k i))
    linarith only [hderivative, hsum k]
  rw [cap_ricci_difference_connection_frame D0 D1 e x hzero i i]
  change |∑ k : Fin 3, ((dB k k i i - dB i k k i) +
    ∑ l : Fin 3, (B k k l * B l i i - B k i l * B l k i))| ≤ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Fin 3, (2 * D + 3 * (2 * (9 * gamma) ^ 2)) :=
      Finset.sum_le_sum fun k _ => hrow k
    _ = _ := by simp [D]; ring

theorem neck_ricci_diagonal_error_small {g0 g1 : RiemannianMetric 3 E}
    (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1) (x : E) (e : E ≃L[ℝ] E)
    (he : ∀ v w : E, g0.inner x (e v) (e w) = inner ℝ v w)
    (hzero : ∀ u v : E, D0.euclideanConnection u v x = 0)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 1200)
    (hbound0 : g0.tensorNorm (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ gamma)
    (hbound1 : g0.tensorNorm (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1))) x ≤ gamma)
    (hbound2 : g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)))) x ≤ gamma)
    (i : Fin 3) :
    |D1.ricci x (e (EuclideanSpace.basisFun (Fin 3) ℝ i))
        (e (EuclideanSpace.basisFun (Fin 3) ℝ i)) -
      D0.ricci x (e (EuclideanSpace.basisFun (Fin 3) ℝ i))
        (e (EuclideanSpace.basisFun (Fin 3) ℝ i))| ≤ 1 / 20 := by
  have h := neck_ricci_diagonal_error_bound D0 D1 x e he hzero hgamma
    (show gamma ≤ 1 / 2 by linarith) hbound0 hbound1 hbound2 i
  have hsquare := pow_le_pow_left₀ hgamma hsmall 2
  nlinarith only [h, hsmall, hsquare]

end PoincareConjecture.Proofs.M47
