import PoincareConjecture.Proofs.M35.TerminalBlowup.RadialConnectionDerivative
import PoincareConjecture.Proofs.M35.Thm12_28.ScalarMetricJets
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.Scalar.Trace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

noncomputable def radialTangentialCurvatureFactor
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  radialConnectionBeta g r - radialConnectionAlpha g r +
    radialConnectionAlpha g r * radialConnectionBeta g r * r ^ 2

noncomputable def radialMixedCurvatureFactor
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  radialConnectionBeta g r + radialConnectionGamma g r * r ^ 2 -
    radialConnectionAlpha g r - r * deriv (radialConnectionAlpha g) r +
    radialConnectionAlpha g r * r ^ 2 *
      (radialConnectionAlpha g r + radialConnectionBeta g r +
        radialConnectionGamma g r * r ^ 2)

theorem rotational_curvature_vectors_axis
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {r : ℝ} (hr : 0 < r) :
    D.curvature (r • e 2) (e 0) (e 1) (e 1) =
        radialTangentialCurvatureFactor g r • e 0 ∧
      D.curvature (r • e 2) (e 0) (e 2) (e 2) =
        radialMixedCurvatureFactor g r • e 0 ∧
      D.curvature (r • e 2) (e 1) (e 2) (e 2) =
        radialMixedCurvatureFactor g r • e 1 := by
  have hx : (r • e 2 : StandardCapSpace) ≠ 0 := by
    intro h
    have hh := congrArg (fun v : StandardCapSpace => v 2) h
    simp only [e, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply,
      if_true, mul_one, PiLp.zero_apply] at hh
    exact hr.ne' hh
  have hn : ‖r • e 2‖ = r := by
    simp [e, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hc (u v : StandardCapSpace) := rotational_connection_const D hrotation hx u v
  have hd (u v w : StandardCapSpace) :=
    rotational_connection_first_derivative D hrotation hx u v w
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [D.curvature_eq_euclideanConnection, hd, hd] <;>
    simp_rw [LeviCivitaData.euclideanConnection, hc] <;>
    simp only [hn, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial] <;>
    change (_ : StandardCapSpace) = (_ : StandardCapSpace) <;>
    ext i <;> fin_cases i <;>
    simp [e, EuclideanSpace.inner_single_right,
      radialTangentialCurvatureFactor, radialMixedCurvatureFactor] <;>
    field_simp [hr.ne'] <;> ring

theorem rotational_sectional_numerators_axis
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {r : ℝ} (hr : 0 < r) :
    D.curvatureTensor (r • e 2) (e 0) (e 1) (e 0) (e 1) =
        axisAngularCoefficient g r * radialTangentialCurvatureFactor g r ∧
      D.curvatureTensor (r • e 2) (e 0) (e 2) (e 0) (e 2) =
        axisAngularCoefficient g r * radialMixedCurvatureFactor g r ∧
      D.curvatureTensor (r • e 2) (e 1) (e 2) (e 1) (e 2) =
        axisAngularCoefficient g r * radialMixedCurvatureFactor g r := by
  obtain ⟨h01, h02, h12⟩ := rotational_curvature_vectors_axis D hrotation hr
  change g.inner _ (D.curvature _ _ _ _) _ = _ ∧
    g.inner _ (D.curvature _ _ _ _) _ = _ ∧
    g.inner _ (D.curvature _ _ _ _) _ = _
  rw [h01, h02, h12]
  simp only [rotational_axis_metric g hrotation, PiLp.smul_apply, smul_eq_mul]
  simp [e]

end PoincareConjecture.M35.Uniqueness
