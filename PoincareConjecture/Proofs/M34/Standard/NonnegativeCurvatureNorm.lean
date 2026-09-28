import PoincareConjecture.Proofs.M04.CurvatureCalculus
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.ThreeDimensional
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData



theorem curvatureTensorNorm_le_scalar_of_nonnegative_sectional
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 3) x, 0 ≤ D.curvatureTensor x v w v w) :
    D.curvatureTensorNorm x ≤ D.scalarCurvature x := by
  obtain ⟨k1, k2, k3, h12, h23, hleast, hscalar, hnorm⟩ :=
    D.three_dimensional_curvature_spectrum D.curvatureTensorCalculus x
  have hk3 : 0 ≤ k3 := by
    rw [← hleast]
    apply Real.sInf_nonneg
    rintro z ⟨v, w, _, rfl⟩
    exact hsec v w
  have hk2 : 0 ≤ k2 := hk3.trans h23
  have hk1 : 0 ≤ k1 := hk2.trans h12
  have hR : 0 ≤ D.scalarCurvature x := by rw [hscalar]; positivity
  have hsq : D.curvatureTensorNorm x ^ 2 ≤ D.scalarCurvature x ^ 2 := by
    rw [hnorm, hscalar]
    nlinarith [mul_nonneg hk1 hk2, mul_nonneg hk1 hk3, mul_nonneg hk2 hk3]
  nlinarith [sq_nonneg (D.curvatureTensorNorm x - D.scalarCurvature x)]

end PoincareConjecture.LeviCivitaData
