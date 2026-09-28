import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.IntrinsicConnection
import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.HarmonicTension









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

theorem mapTension_intrinsic_axis
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hcomplete : MetricComplete g)
    (D : LeviCivitaData (intrinsicSpatialMetric g hrotation hcomplete))
    {b : RiemannianMetric 3 StandardCapSpace} (B : LeviCivitaData b)
    (F : StandardCapSpace → StandardCapSpace) (r : ℝ) :
    mapTension D B F (r • e 2) =
      (intrinsicWarpingQuotient g hrotation hcomplete r ^ 2)⁻¹ •
        mapCovariantHessian D B F (r • e 2) (e 0) (e 0) +
      (intrinsicWarpingQuotient g hrotation hcomplete r ^ 2)⁻¹ •
        mapCovariantHessian D B F (r • e 2) (e 1) (e 1) +
      mapCovariantHessian D B F (r • e 2) (e 2) (e 2) := by
  let Q := intrinsicWarpingQuotient g hrotation hcomplete r
  let w : Fin 3 → ℝ := ![Q ^ 2, Q ^ 2, 1]
  let E : Module.Basis (Fin 3) ℝ StandardCapSpace :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hE (i : Fin 3) : E i = e i := EuclideanSpace.basisFun_apply (Fin 3) ℝ i
  have hgram : Matrix.of (fun i j : Fin 3 =>
      (intrinsicSpatialMetric g hrotation hcomplete).inner (r • e 2) (E i) (E j)) =
        Matrix.diagonal w := by
    ext i j
    simp only [Matrix.of_apply, hE, rotational_axis_metric _
      (intrinsicSpatialMetric_rotation g hrotation hcomplete),
      intrinsicSpatialMetric_axisAngularCoefficient, intrinsicSpatialMetric_axisRadialCoefficient]
    fin_cases i <;> fin_cases j <;> simp [e, w, Q, Matrix.diagonal]
  have hw (i : Fin 3) : w i ≠ 0 := by
    fin_cases i
    · exact pow_ne_zero 2 (intrinsicWarpingQuotient_pos g hrotation hcomplete r).ne'
    · exact pow_ne_zero 2 (intrinsicWarpingQuotient_pos g hrotation hcomplete r).ne'
    · exact one_ne_zero
  have hunit : IsUnit w := Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hw i))
  have hinv (i : Fin 3) : Ring.inverse w i = (w i)⁻¹ := by
    have h := congrFun (Ring.inverse_mul_cancel w hunit) i
    rw [← one_div]
    exact (eq_div_iff (hw i)).mpr h
  rw [mapTension_eq_inverse_gram D B F _ E, hgram, Matrix.inv_diagonal]
  simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, hinv, hE, Fin.sum_univ_succ, Fin.sum_univ_zero,
    w, Matrix.cons_val_zero, Matrix.cons_val_succ, inv_one, one_smul, add_zero]
  abel

end PoincareConjecture.M35.Uniqueness
