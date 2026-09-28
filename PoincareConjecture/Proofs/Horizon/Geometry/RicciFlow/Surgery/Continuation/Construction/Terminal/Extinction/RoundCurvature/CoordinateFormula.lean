import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Ricci








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem fderiv_bilinear_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : E → E →L[ℝ] E →L[ℝ] F} {x : E}
    (hA : DifferentiableAt ℝ A x) (u v w : E) :
    fderiv ℝ (fun y => A y v w) x u = fderiv ℝ A x u v w := by
  have h := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply
    (hasFDerivAt_const w x)
  simpa using congrArg (fun L => L u) h.fderiv

private theorem metric_fderiv_apply (x a b c : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => g.inner y b c) x a =
      fderiv ℝ g.euclideanCoefficients x a b c :=
  fderiv_bilinear_apply ((g.contDiffAt_euclideanCoefficients x).differentiableAt
    (by simp)) a b c

private theorem metric_fderiv_symm (x a b c : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ g.euclideanCoefficients x a b c =
      fderiv ℝ g.euclideanCoefficients x a c b := by
  rw [← metric_fderiv_apply, ← metric_fderiv_apply]
  congr 2
  exact funext fun y => g.symm y b c

theorem metric_fderiv_eq_connection_pairings (D : LeviCivitaData g)
    (x a b c : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ g.euclideanCoefficients x a b c =
      g.inner x (D.euclideanConnection a b x) c +
        g.inner x b (D.euclideanConnection a c x) := by
  have h₁ := D.inner_connection_const x a b c
  have h₂ := D.inner_connection_const x a c b
  rw [metric_fderiv_apply, metric_fderiv_apply, metric_fderiv_apply] at h₁ h₂
  rw [metric_fderiv_symm x a c b, metric_fderiv_symm x c b a] at h₂
  rw [metric_fderiv_symm x b c a] at h₁
  rw [g.symm x b]
  change 2 * g.inner x (D.euclideanConnection a b x) c = _ at h₁
  change 2 * g.inner x (D.euclideanConnection a c x) b = _ at h₂
  linarith


theorem curvatureTensor_eq_second_deriv_add_connection_pairings (D : LeviCivitaData g)
    (x u b v c : EuclideanSpace ℝ (Fin n)) :
    D.curvatureTensor x u b v c =
      (2⁻¹ : ℝ) *
        (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x u c b v -
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x u v b c -
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x b c u v +
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x b v u c) +
      (g.inner x (D.euclideanConnection u c x) (D.euclideanConnection b v x) -
        g.inner x (D.euclideanConnection b c x) (D.euclideanConnection u v x)) := by
  rw [D.curvatureTensor_eq_metric_second_deriv,
    D.metric_fderiv_eq_connection_pairings x u (D.euclideanConnection b c x) v,
    D.metric_fderiv_eq_connection_pairings x b (D.euclideanConnection u c x) v]
  ring

private theorem covector_eq_sum (A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    A = ∑ i, A (EuclideanSpace.basisFun (Fin n) ℝ i) • EuclideanSpace.proj i := by
  ext v
  have h := congrArg A ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, sum_apply,
    smul_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    PiLp.proj_apply, mul_comm] using h.symm

theorem inner_inverse_eq_sum_inverseCoefficients (x : EuclideanSpace ℝ (Fin n))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    g.euclideanCoefficients x ((g.euclideanCoefficients x).inverse A)
        ((g.euclideanCoefficients x).inverse B) =
      ∑ i, ∑ j, g.inverseCoefficients x i j *
        A (EuclideanSpace.basisFun (Fin n) ℝ i) *
        B (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hinv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  rw [hinv.self_apply_inverse]
  conv_lhs => arg 1; rw [covector_eq_sum A]
  conv_lhs => arg 2; arg 2; rw [covector_eq_sum B]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change B (EuclideanSpace.basisFun (Fin n) ℝ j) *
    (A (EuclideanSpace.basisFun (Fin n) ℝ i) * g.inverseCoefficients x j i) = _
  rw [g.inverseCoefficients_symm x j i]
  ring


theorem curvatureTensor_eq_second_deriv_add_firstKind (D : LeviCivitaData g)
    (x u b v c : EuclideanSpace ℝ (Fin n)) :
    D.curvatureTensor x u b v c =
      (2⁻¹ : ℝ) *
        (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x u c b v -
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x u v b c -
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x b c u v +
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x b v u c) +
      ∑ i, ∑ j, g.inverseCoefficients x i j *
        (metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) u c
            (EuclideanSpace.basisFun (Fin n) ℝ i) *
          metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) b v
            (EuclideanSpace.basisFun (Fin n) ℝ j) -
          metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) b c
            (EuclideanSpace.basisFun (Fin n) ℝ i) *
          metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) u v
            (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  rw [D.curvatureTensor_eq_second_deriv_add_connection_pairings]
  have hpair (a b c d : EuclideanSpace ℝ (Fin n)) :
      g.inner x (D.euclideanConnection a b x) (D.euclideanConnection c d x) =
        ∑ i, ∑ j, g.inverseCoefficients x i j *
          metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) a b
            (EuclideanSpace.basisFun (Fin n) ℝ i) *
          metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) c d
            (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    simp only [euclideanConnection, D.connection_const_eq_inverse]
    exact inner_inverse_eq_sum_inverseCoefficients x _ _
  simp only [hpair, mul_sub, Finset.sum_sub_distrib, mul_assoc]

end PoincareConjecture.LeviCivitaData
