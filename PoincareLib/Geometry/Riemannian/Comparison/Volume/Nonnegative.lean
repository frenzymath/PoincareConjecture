import PoincareLib.Geometry.Riemannian.Comparison.Volume.Injectivity
import PoincareLib.Geometry.Riemannian.Soul.Injectivity

/-!
# Uniform unit-ball volume under bounded nonnegative sectional curvature

The convex exhaustion and short-loop argument produce a positive uniform
injectivity radius. Jacobi comparison on a smaller ball and the volume
change-of-variables formula give the requested positive volume constant.

Reference: Maeder--Baumdicker--Seidel, Theorem 1 and Remark 1.1, p. 4.
The volume statement is an auxiliary consequence of their injectivity bound.
-/

set_option autoImplicit false

open scoped Manifold ContDiff ENNReal Bundle

namespace PoincareMT.RiemannianMetric

set_option linter.unusedVariables false in
/-- Every complete connected manifold with bounded nonnegative sectional
curvature has a positive uniform lower bound for the volume of its unit balls.
The constant is allowed to depend on the entire manifold and metric. -/
theorem exists_uniform_unit_ball_volume_lower_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hn : 1 ≤ n) (hcomplete : MetricComplete g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x (u v : TangentSpace (𝓡 n) x),
      0 ≤ D.sectionalCurvature x u v ∧ D.sectionalCurvature x u v ≤ K) :
    ∃ v : ℝ, 0 < v ∧ ∀ x : M,
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball x 1) := by
  clear hn
  have hnonneg : D.NonnegativeSectionalCurvature := by
    intro x u v
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    rw [D.curvatureTensor_diagonal_eq_sectional_mul_gram]
    apply mul_nonneg (hsec x u v).1
    change 0 ≤ inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2
    simpa only [pow_two] using sub_nonneg.mpr (real_inner_mul_inner_self_le u v)
  have habs (x : M) (u v : TangentSpace (𝓡 n) x) :
      |D.sectionalCurvature x u v| ≤ K := by
    rw [abs_of_nonneg (hsec x u v).1]
    exact (hsec x u v).2
  let K' := 4 * (n : ℝ) ^ 2 * K
  have hK' : 0 ≤ K' := by dsimp [K']; positivity
  have hcurv (x : M) : D.curvatureTensorNorm x ≤ K' :=
    D.curvatureTensorNorm_le_of_sectional x hK (habs x)
  let C := Poincare.ODE.Jacobi.comparisonRadius K' / 2
  have hC : 0 < C := half_pos (Poincare.ODE.Jacobi.comparisonRadius_pos K')
  have hCK : 2 * C ≤ Poincare.ODE.Jacobi.comparisonRadius K' := by
    dsimp [C]
    linarith
  obtain ⟨ρ, hρ, hinj⟩ :=
    g.exists_pos_le_truncatedInjectivityRadius_of_nonnegativeSectional D hcomplete
      hnonneg hK' hcurv hC hCK
  exact g.exists_uniform_unit_ball_volume_lower_bound_of_injectivity D hcomplete
    hK hC.le hρ habs hinj

end PoincareMT.RiemannianMetric
