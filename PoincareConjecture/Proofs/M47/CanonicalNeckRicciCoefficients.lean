import PoincareConjecture.Proofs.M47.BlowupControlsCapConnectionDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.NormBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem frame_tangentNorm (g : RiemannianMetric 3 E) (x : E)
    (e : E ≃L[ℝ] E) (he : ∀ v w : E, g.inner x (e v) (e w) = inner ℝ v w)
    (v : E) : g.tangentNorm x (e v) = ‖v‖ := by
  change Real.sqrt (g.inner x (e v) (e v)) = ‖v‖
  rw [he, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]



theorem neck_tensor_component_bound (g : RiemannianMetric 3 E) (x : E)
    (e : E ≃L[ℝ] E) (he : ∀ v w : E, g.inner x (e v) (e w) = inner ℝ v w)
    {r : ℕ} (T : CovariantTensorEvaluation 3 E r) (hT : IsSmoothCovariantTensor T)
    {gamma : ℝ} (hbound : g.tensorNorm T x ≤ gamma) (a : Fin r → Fin 3) :
    |T x (fun j => e (EuclideanSpace.basisFun (Fin 3) ℝ (a j)))| ≤ gamma := by
  obtain ⟨A, hA⟩ := hT.1 x
  have h := abs_tensor_evaluation_le_tensorNorm g T x A hA
    (fun j => e (EuclideanSpace.basisFun (Fin 3) ℝ (a j)))
  simp only [frame_tangentNorm g x e he, OrthonormalBasis.norm_eq_one,
    Finset.prod_const_one, mul_one] at h
  exact h.trans hbound

private theorem coefficient_le_norm (A : E →L[ℝ] E) (i j : Fin 3) :
    |inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (A (EuclideanSpace.basisFun (Fin 3) ℝ j))| ≤ ‖A‖ := by
  have h := abs_real_inner_le_norm (EuclideanSpace.basisFun (Fin 3) ℝ i)
    (A (EuclideanSpace.basisFun (Fin 3) ℝ j))
  simp only [OrthonormalBasis.norm_eq_one, one_mul] at h
  have ha := A.le_opNorm (EuclideanSpace.basisFun (Fin 3) ℝ j)
  exact h.trans (by simpa only [OrthonormalBasis.norm_eq_one, mul_one] using ha)

private theorem operator_norm_le_nine (A : E →L[ℝ] E) {gamma : ℝ}
    (_hgamma : 0 ≤ gamma)
    (hA : ∀ i j : Fin 3,
      |inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (A (EuclideanSpace.basisFun (Fin 3) ℝ j))| ≤ gamma) :
    ‖A‖ ≤ 9 * gamma := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hcolumn (j : Fin 3) : ‖A (b j)‖ ≤ 3 * gamma := by
    conv_lhs => rw [← b.sum_repr (A (b j))]
    calc
      _ ≤ ∑ i : Fin 3, ‖b.repr (A (b j)) i • b i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, gamma := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [norm_smul, Real.norm_eq_abs, OrthonormalBasis.norm_eq_one,
          mul_one, b.repr_apply_apply] using hA i j
      _ = _ := by simp
  have hexpand : A = ∑ j : Fin 3, (innerSL ℝ (b j)).smulRight (A (b j)) := by
    ext v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, sum_apply, ContinuousLinearMap.smulRight_apply,
      b.repr_apply_apply, innerSL_apply_apply]
  rw [hexpand]
  calc
    _ ≤ ∑ j : Fin 3, ‖(innerSL ℝ (b j)).smulRight (A (b j))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, 3 * gamma := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = ‖innerSL ℝ (b j)‖ * ‖A (b j)‖ := ContinuousLinearMap.norm_smulRight_apply _ _
        _ ≤ 1 * (3 * gamma) := mul_le_mul (by simp [b]) (hcolumn j)
          (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = _ := by simp; ring


theorem neck_frame_inverse_bound {g0 g1 : RiemannianMetric 3 E}
    (x : E) (e : E ≃L[ℝ] E)
    (he : ∀ v w : E, g0.inner x (e v) (e w) = inner ℝ v w)
    {gamma : ℝ} (hsmall : gamma ≤ 1 / 2)
    (hbound : g0.tensorNorm (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ gamma) :
    ‖(M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse‖ ≤ 2 ∧
      ∀ i j : Fin 3, |M04.frameInverseGram g1 x e.toContinuousLinearMap i j| ≤ 2 := by
  let H : CovariantTensorEvaluation 3 E 2 :=
    fun y v => g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  change g0.tensorNorm H x ≤ gamma at hbound
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth g0 g1
  obtain ⟨A, hA⟩ := hH.1 x
  have hlower (v : E) : (1 - gamma) * ‖v‖ ^ 2 ≤ g1.inner x (e v) (e v) := by
    have h := abs_tensor_evaluation_le_tensorNorm g0 H x A hA ![e v, e v]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      frame_tangentNorm g0 x e he] at h
    have hb := mul_le_mul_of_nonneg_right hbound (mul_self_nonneg ‖v‖)
    change |g1.inner x (e v) (e v) - g0.inner x (e v) (e v)| ≤ _ at h
    rw [he, real_inner_self_eq_norm_sq] at h
    nlinarith [(abs_le.mp h).1]
  have hnorm := cap_frameInverseGram_norm_le g1 x e
    (show gamma < 1 by linarith) hlower
  have htwo : (1 - gamma)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - gamma)).mpr
    linarith
  have hn := hnorm.trans htwo
  refine ⟨hn, fun i j => ?_⟩
  exact (coefficient_le_norm _ i j).trans hn



theorem neck_frame_inverse_derivative_bound {g0 g1 : RiemannianMetric 3 E}
    (D0 : LeviCivitaData g0) (x : E) (e : E ≃L[ℝ] E)
    (he : ∀ v w : E, g0.inner x (e v) (e w) = inner ℝ v w)
    (hzero : ∀ u v : E, D0.euclideanConnection u v x = 0)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 2)
    (hbound0 : g0.tensorNorm (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ gamma)
    (hbound1 : g0.tensorNorm (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1))) x ≤ gamma)
    (i j k : Fin 3) :
    |fderiv ℝ (fun y => M04.frameInverseGram g1 y e.toContinuousLinearMap i j) x
      (e (EuclideanSpace.basisFun (Fin 3) ℝ k))| ≤ 36 * gamma := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let G : E → E →L[ℝ] E := fun y => M04.frameGramOperator g1 y e.toContinuousLinearMap
  let H : CovariantTensorEvaluation 3 E 2 :=
    fun y v => g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth g0 g1
  have hH1 := M04.isSmoothCovariantTensor_covariantTensorDerivative D0 hH
  have hG : DifferentiableAt ℝ G x :=
    (cap_frameGram_contDiff g1 e.toContinuousLinearMap).differentiable (by simp) x
  have hdG : ‖fderiv ℝ G x (e (b k))‖ ≤ 9 * gamma := by
    apply operator_norm_le_nine _ hgamma
    intro a c
    rw [real_inner_comm]
    have hread := cap_frameGram_fderiv_normal (g1 := g1) D0 e x hzero (e (b k)) (b c) (b a)
    change inner ℝ (fderiv ℝ G x (e (b k)) (b c)) (b a) = _ at hread
    rw [hread]
    exact neck_tensor_component_bound g0 x e he (D0.covariantTensorDerivative H) hH1
      hbound1 ![k, c, a]
  have hinverse := (neck_frame_inverse_bound x e he hsmall hbound0).1
  have hd := cap_inverse_fderiv_norm_le G hG
    (M04.frameGramOperator_isInvertible g1 x e) (by norm_num : (0 : ℝ) ≤ 2)
    hinverse (e (b k))
  have hdBound : ‖fderiv ℝ (fun y => (G y).inverse) x (e (b k))‖ ≤ 36 * gamma := by
    nlinarith only [hd, hdG]
  rw [cap_frameInverseGram_fderiv g1 e x]
  have hread := cap_inverse_fderiv_apply G hG
    (M04.frameGramOperator_isInvertible g1 x e) (e (b k))
  change |inner ℝ (b i) ((-((G x).inverse * (fderiv ℝ G x (e (b k))) *
    (G x).inverse)) (b j))| ≤ _
  rw [← hread]
  exact (coefficient_le_norm _ i j).trans hdBound

end PoincareConjecture.Proofs.M47
