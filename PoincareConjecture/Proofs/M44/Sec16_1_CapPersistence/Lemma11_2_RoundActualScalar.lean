import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_CurvatureDefectBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundScalarLower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem scalarCurvature_three_le_of_round_metric_error {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : E) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hcurv : D.curvatureTensorNorm x ≤ 9)
    (hgram : ∀ u v : E, D.curvatureTensor x u v u v =
      g.inner x u u * g.inner x v v - g.inner x u v ^ 2)
    (herror : ∀ j ≤ 2,
      g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) j) x ≤ epsilon) :
    3 ≤ D'.scalarCurvature x := by
  have hmetric (u v : E) : |h.inner x u v - g.inner x u v| ≤
      epsilon * (g.tangentNorm x u * g.tangentNorm x v) := by
    simpa! only [Nat.add_zero, LeviCivitaData.iteratedCovariantTensorDerivative, metricError,
      Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
      metricError_jet_evaluation_le D 0 x (herror 0 (by omega)) ![u, v]
  have hquad (v : E) : g.tangentNorm x v ^ 2 = g.inner x v v := by
    apply Real.sq_sqrt
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hplane (u v : E) : |D'.curvatureTensor x u v u v -
      (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)| ≤
        13 * epsilon * (g.inner x u u * g.inner x v v) := by
    have hh := abs_curvatureTensor_difference_le D D' x hepsilon
      (show epsilon ≤ 1 / 4 by linarith) hcurv herror u v u v
    rw [hgram] at hh
    have hp : g.tangentNorm x u * g.tangentNorm x v *
        g.tangentNorm x u * g.tangentNorm x v = g.inner x u u * g.inner x v v := by
      rw [← hquad, ← hquad]
      ring
    rw [hp] at hh
    have hcoeff : (9 + 3 : ℝ) * epsilon + 10 * epsilon ^ 2 ≤ 13 * epsilon := by
      nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right hcoeff (by
      rw [← hquad, ← hquad]
      positivity))
  apply scalarCurvature_three_le_of_sectional_half D' x
  intro u v huv
  exact sectional_half_le_of_round_plane_error D' x hepsilon hsmall hmetric hplane u v huv

end PoincareConjecture.M44
