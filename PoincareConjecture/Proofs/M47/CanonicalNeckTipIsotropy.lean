import PoincareConjecture.Proofs.M47.CanonicalNeckRicciDiagonals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem neck_reference_ricci_not_isotropic {g0 g1 : RiemannianMetric 3 E}
    (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1) (x : E) (e : E ≃L[ℝ] E)
    (he : ∀ v w : E, g0.inner x (e v) (e w) = inner ℝ v w)
    (hzero : ∀ u v : E, D0.euclideanConnection u v x = 0)
    (hangular : D0.ricci x (e (EuclideanSpace.basisFun (Fin 3) ℝ 0))
      (e (EuclideanSpace.basisFun (Fin 3) ℝ 0)) = 1 / 2)
    (haxial : D0.ricci x (e (EuclideanSpace.basisFun (Fin 3) ℝ 2))
      (e (EuclideanSpace.basisFun (Fin 3) ℝ 2)) = 0)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 1200)
    (hbound0 : g0.tensorNorm (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ gamma)
    (hbound1 : g0.tensorNorm (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1))) x ≤ gamma)
    (hbound2 : g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)))) x ≤ gamma) :
    ¬ (∀ u v : E,
      D1.ricci x u u * g1.inner x v v = D1.ricci x v v * g1.inner x u u) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let H : CovariantTensorEvaluation 3 E 2 :=
    fun y v => g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth g0 g1
  have hmetric (i : Fin 3) :
      1 / 2 ≤ g1.inner x (e (b i)) (e (b i)) ∧
        g1.inner x (e (b i)) (e (b i)) ≤ 3 / 2 := by
    have h := neck_tensor_component_bound g0 x e he H hH hbound0 ![i, i]
    change |g1.inner x (e (b i)) (e (b i)) - g0.inner x (e (b i)) (e (b i))| ≤ gamma at h
    rw [he] at h
    have hunit : inner ℝ (b i) (b i) = 1 := by simp [b]
    rw [hunit] at h
    constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]
  have hang := neck_ricci_diagonal_error_small D0 D1 x e he hzero hgamma hsmall
    hbound0 hbound1 hbound2 0
  have haxis := neck_ricci_diagonal_error_small D0 D1 x e he hzero hgamma hsmall
    hbound0 hbound1 hbound2 2
  rw [hangular] at hang
  rw [haxial, sub_zero] at haxis
  have hRang : 9 / 20 ≤ D1.ricci x (e (b 0)) (e (b 0)) := by
    linarith [(abs_le.mp hang).1]
  have hRaxis : D1.ricci x (e (b 2)) (e (b 2)) ≤ 1 / 20 := (abs_le.mp haxis).2
  have hlower : (9 / 40 : ℝ) ≤
      D1.ricci x (e (b 0)) (e (b 0)) * g1.inner x (e (b 2)) (e (b 2)) := by
    have h := mul_le_mul hRang (hmetric 2).1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith only [hRang] : 0 ≤ D1.ricci x (e (b 0)) (e (b 0)))
    norm_num at h ⊢
    exact h
  have hupper : D1.ricci x (e (b 2)) (e (b 2)) *
      g1.inner x (e (b 0)) (e (b 0)) ≤ (3 / 40 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hRaxis
      (show 0 ≤ g1.inner x (e (b 0)) (e (b 0)) by linarith [(hmetric 0).1])
    have h2 := mul_le_mul_of_nonneg_left (hmetric 0).2 (by norm_num : (0 : ℝ) ≤ 1 / 20)
    linarith only [h1, h2]
  intro hisotropic
  have heq := hisotropic (e (b 0)) (e (b 2))
  linarith only [hlower, hupper, heq]

end PoincareConjecture.Proofs.M47
