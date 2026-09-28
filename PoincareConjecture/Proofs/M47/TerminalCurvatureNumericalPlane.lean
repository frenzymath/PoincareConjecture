import PoincareConjecture.Proofs.M47.TerminalCurvatureNumericalComponents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

open PoincareConjecture.Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_calibrated_angular_plane
    {g0 g1 : RiemannianMetric 3 E} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (x : E) (e : E ≃L[ℝ] E)
    (he : ∀ v w : E, g0.inner x (e v) (e w) = inner ℝ v w)
    (hzero : ∀ u v : E, D0.euclideanConnection u v x = 0)
    (hmodel : D0.curvature x (e (EuclideanSpace.basisFun (Fin 3) ℝ 0))
      (e (EuclideanSpace.basisFun (Fin 3) ℝ 1)) (e (EuclideanSpace.basisFun (Fin 3) ℝ 1)) =
        (1 / 2 : ℝ) • e (EuclideanSpace.basisFun (Fin 3) ℝ 0))
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 200)
    (hbound0 : g0.tensorNorm (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ gamma)
    (hbound1 : g0.tensorNorm (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1))) x ≤ gamma)
    (hbound2 : g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)))) x ≤ gamma) :
    (1 / 4 : ℝ) < D1.curvatureTensor x
      (e (EuclideanSpace.basisFun (Fin 3) ℝ 0)) (e (EuclideanSpace.basisFun (Fin 3) ℝ 1))
      (e (EuclideanSpace.basisFun (Fin 3) ℝ 0)) (e (EuclideanSpace.basisFun (Fin 3) ℝ 1)) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let K := 18 * gamma + 810 * gamma ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let delta : E := D1.curvature x (e (b 0)) (e (b 1)) (e (b 1)) -
    D0.curvature x (e (b 0)) (e (b 1)) (e (b 1))
  have hdelta (i : Fin 3) : |inner ℝ (b i) (e.symm delta)| ≤ K :=
    terminalCurvature_numerical_curvature_component D0 D1 x e he hzero hgamma
      (hsmall.trans (by norm_num)) hbound0 hbound1 hbound2 0 1 1 i
  let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
    g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth _ _
  have hmetric (i : Fin 3) :
      |g1.inner x (e (b i)) (e (b 0)) - inner ℝ (b i) (b 0)| ≤ gamma := by
    have hh := neck_tensor_component_bound g0 x e he H hH hbound0 ![i, 0]
    simpa only [H, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, he]
      using hh
  have hgram (i : Fin 3) :
      |g1.inner x (e (b i)) (e (b 0))| ≤ |inner ℝ (b i) (b 0)| + gamma := by
    have hh := abs_add_le (g1.inner x (e (b i)) (e (b 0)) - inner ℝ (b i) (b 0))
      (inner ℝ (b i) (b 0))
    rw [sub_add_cancel] at hh
    linarith only [hh, hmetric i]
  have hrec : (∑ i : Fin 3, inner ℝ (b i) (e.symm delta) • e (b i)) = delta := by
    calc
      _ = e (∑ i : Fin 3, inner ℝ (b i) (e.symm delta) • b i) := by
        simp only [map_sum, map_smul]
      _ = e (e.symm delta) := congrArg e (b.sum_repr' (e.symm delta))
      _ = delta := e.apply_symm_apply delta
  have hpairEq : g1.inner x delta (e (b 0)) =
      ∑ i : Fin 3, inner ℝ (b i) (e.symm delta) * g1.inner x (e (b i)) (e (b 0)) := by
    conv_lhs => rw [← hrec]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  have hpair : |g1.inner x delta (e (b 0))| ≤ (1 + 3 * gamma) * K := by
    rw [hpairEq]
    calc
      _ ≤ ∑ i : Fin 3,
          |inner ℝ (b i) (e.symm delta) * g1.inner x (e (b i)) (e (b 0))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, K * (|inner ℝ (b i) (b 0)| + gamma) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hdelta i) (hgram i) (abs_nonneg _) hK
      _ = _ := by
        simp [b.inner_eq_ite, Fin.sum_univ_succ]
        ring
  have hdiag : |g1.inner x (e (b 0)) (e (b 0)) - 1| ≤ gamma := by
    simpa only [b.inner_eq_ite, ite_true] using hmetric 0
  have hR : D1.curvature x (e (b 0)) (e (b 1)) (e (b 1)) =
      delta + (1 / 2 : ℝ) • e (b 0) := by
    dsimp only [delta]
    rw [← hmodel]
    exact (sub_add_cancel _ _).symm
  have herror : D1.curvatureTensor x (e (b 0)) (e (b 1)) (e (b 0)) (e (b 1)) - 1 / 2 =
      g1.inner x delta (e (b 0)) + (1 / 2 : ℝ) * (g1.inner x (e (b 0)) (e (b 0)) - 1) := by
    rw [LeviCivitaData.curvatureTensor, hR]
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
    ring
  have habs : |D1.curvatureTensor x (e (b 0)) (e (b 1)) (e (b 0)) (e (b 1)) - 1 / 2| ≤
      (1 + 3 * gamma) * K + gamma / 2 := by
    rw [herror]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hd := mul_le_mul_of_nonneg_left hdiag (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith only [hpair, hd]
  have hn : (1 + 3 * gamma) * K + gamma / 2 < 1 / 4 := by
    dsimp only [K]
    calc
      _ ≤ (1 + 3 * (1 / 200 : ℝ)) *
          (18 * (1 / 200) + 810 * (1 / 200) ^ 2) + (1 / 200) / 2 := by gcongr
      _ < _ := by norm_num
  have hlo := (abs_le.mp habs).1
  change (1 / 4 : ℝ) < D1.curvatureTensor x (e (b 0)) (e (b 1)) (e (b 0)) (e (b 1))
  linarith only [hlo, hn]

end PoincareConjecture.M47
