import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Sectional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem inner_radialCurvature_ge_of_sectional_lower_bound
    (D : LeviCivitaData g) (x : M) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x, -K ≤ D.sectionalCurvature x u v)
    (u v : TangentSpace (𝓡 n) x) :
    -K * g.inner x u u * g.inner x v v ≤
      g.inner x (D.curvature x u v v) u := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgram : 0 ≤ g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    have h := real_inner_mul_inner_self_le u v
    change g.inner x u v * g.inner x u v ≤ g.inner x u u * g.inner x v v at h
    nlinarith
  change _ ≤ D.curvatureTensor x u v u v
  rw [D.curvatureTensor_diagonal_eq_sectional_mul_gram]
  have h := mul_le_mul_of_nonneg_right (hsec u v) hgram
  nlinarith [mul_nonneg hK (sq_nonneg (g.inner x u v))]

end PoincareConjecture.LeviCivitaData
