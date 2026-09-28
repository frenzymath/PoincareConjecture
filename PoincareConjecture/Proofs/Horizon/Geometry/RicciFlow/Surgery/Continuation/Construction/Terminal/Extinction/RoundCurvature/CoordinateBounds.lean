import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CoordinateFormula

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem iteratedFDeriv_metric_inner (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (r : ℕ) (x u v : EuclideanSpace ℝ (Fin n))
    (a : Fin r → EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ r (fun y => g.inner y u v) x a =
      iteratedFDeriv ℝ r g.euclideanCoefficients x a u v := by
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  change iteratedFDeriv ℝ r (fun y => g.euclideanCoefficients y u v) x a = _
  rw [iteratedFDeriv_clm_apply_const_apply (hg.clm_apply contDiff_const)
      (WithTop.coe_le_coe.mpr le_top),
    iteratedFDeriv_clm_apply_const_apply hg (WithTop.coe_le_coe.mpr le_top)]

theorem iteratedFDeriv_one_metric_inner
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x a u v : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 1 (fun y => g.inner y u v) x ![a] =
      fderiv ℝ g.euclideanCoefficients x a u v := by
  rw [iteratedFDeriv_metric_inner, iteratedFDeriv_one_apply]
  rfl

theorem iteratedFDeriv_two_metric_inner
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x a b u v : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2 (fun y => g.inner y u v) x ![a, b] =
      fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a b u v := by
  rw [iteratedFDeriv_metric_inner, iteratedFDeriv_two_apply]
  rfl

theorem abs_metricKoszulCovector_basis_le
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    {a : ℝ} (hB : ∀ i j k, |B (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ k)| ≤ a)
    (i j k : Fin n) :
    |metricKoszulCovector B (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ k)| ≤
      (3 / 2 : ℝ) * a := by
  have h₁ := abs_le.mp (hB i j k)
  have h₂ := abs_le.mp (hB j k i)
  have h₃ := abs_le.mp (hB k i j)
  simp only [metricKoszulCovector, smul_apply, sub_apply, add_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [abs_le]
  constructor <;> linarith

theorem abs_curvatureTensor_sub_le_of_centered_jets
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    (x : EuclideanSpace ℝ (Fin n)) {a b C : ℝ} (ha : 0 ≤ a)
    (hzero : fderiv ℝ g.euclideanCoefficients x = 0)
    (hfirst : ∀ i j k, |fderiv ℝ h.euclideanCoefficients x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
      (EuclideanSpace.basisFun (Fin n) ℝ k)| ≤ a)
    (hsecond : ∀ i j k l,
      |fderiv ℝ (fderiv ℝ h.euclideanCoefficients) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) (EuclideanSpace.basisFun (Fin n) ℝ l) -
       fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) (EuclideanSpace.basisFun (Fin n) ℝ l)| ≤ b)
    (hinverse : (∑ i, ∑ j, |h.inverseCoefficients x i j|) ≤ C)
    (i j k l : Fin n) :
    |Dh.curvatureTensor x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ k)
        (EuclideanSpace.basisFun (Fin n) ℝ l) -
      Dg.curvatureTensor x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ k)
        (EuclideanSpace.basisFun (Fin n) ℝ l)| ≤
      2 * b + (9 / 2 : ℝ) * C * a ^ 2 := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let K (i j k : Fin n) := metricKoszulCovector
    (fderiv ℝ h.euclideanCoefficients x) (e i) (e j) (e k)
  have hK (i j k : Fin n) : |K i j k| ≤ (3 / 2 : ℝ) * a :=
    abs_metricKoszulCovector_basis_le _ hfirst i j k
  have hprod (i j k l p q : Fin n) :
      |K i j p * K k l q| ≤ ((3 / 2 : ℝ) * a) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hK i j p) (hK k l q) (abs_nonneg _) (by positivity)
  have hpair (p q : Fin n) :
      |K i l p * K j k q - K j l p * K i k q| ≤ (9 / 2 : ℝ) * a ^ 2 := by
    calc
      _ ≤ |K i l p * K j k q| + |K j l p * K i k q| := abs_sub _ _
      _ ≤ ((3 / 2 : ℝ) * a) ^ 2 + ((3 / 2 : ℝ) * a) ^ 2 :=
        add_le_add (hprod i l j k p q) (hprod j l i k p q)
      _ = _ := by ring
  have hquad :
      |∑ p, ∑ q, h.inverseCoefficients x p q *
        (K i l p * K j k q - K j l p * K i k q)| ≤ (9 / 2 : ℝ) * C * a ^ 2 := by
    calc
      _ ≤ ∑ p, |∑ q, h.inverseCoefficients x p q *
        (K i l p * K j k q - K j l p * K i k q)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p, ∑ q, |h.inverseCoefficients x p q| * ((9 / 2 : ℝ) * a ^ 2) := by
        apply Finset.sum_le_sum
        intro p _
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpair p q) (abs_nonneg _)
      _ = (∑ p, ∑ q, |h.inverseCoefficients x p q|) * ((9 / 2 : ℝ) * a ^ 2) := by
        simp only [Finset.sum_mul]
      _ ≤ C * ((9 / 2 : ℝ) * a ^ 2) :=
        mul_le_mul_of_nonneg_right hinverse (by positivity)
      _ = _ := by ring
  have hlin₁ := abs_le.mp (hsecond i l j k)
  have hlin₂ := abs_le.mp (hsecond i k j l)
  have hlin₃ := abs_le.mp (hsecond j l i k)
  have hlin₄ := abs_le.mp (hsecond j k i l)
  have hquad' := abs_le.mp hquad
  rw [Dh.curvatureTensor_eq_second_deriv_add_firstKind,
    Dg.curvatureTensor_eq_second_deriv_add_firstKind]
  simp only [hzero, metricKoszulCovector, zero_apply,
    ContinuousLinearMap.flip_zero, add_zero, sub_zero, smul_zero,
    mul_zero, Finset.sum_const_zero]
  change |_ + (∑ p, ∑ q, h.inverseCoefficients x p q *
    (K i l p * K j k q - K j l p * K i k q)) - _| ≤ _
  rw [abs_le]
  constructor <;> linarith

end PoincareConjecture.LeviCivitaData
