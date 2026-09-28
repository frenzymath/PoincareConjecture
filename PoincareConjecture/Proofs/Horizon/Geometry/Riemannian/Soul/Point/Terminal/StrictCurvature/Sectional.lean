import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureTensor_diagonal_pos_of_orthonormal
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v)
    {u v : TangentSpace (𝓡 n) x} (hxy : LinearIndependent ℝ ![u, v]) :
    0 < D.curvatureTensor x u v u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨a, b, c, d, hdet, hp, hq, hpq⟩ :=
    exists_orthonormal_changeBasis u v hxy
  have hnum : D.curvatureTensor x (a • u + b • v) (c • u + d • v)
      (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := by
    simp only [curvatureTensor_add_first, curvatureTensor_add_second,
      curvatureTensor_add_third, curvatureTensor_add_last,
      curvatureTensor_smul_first, curvatureTensor_smul_second,
      curvatureTensor_smul_third, curvatureTensor_smul_last,
      curvatureTensor_zero_first, curvatureTensor_zero_last]
    rw [curvatureTensor_swap_first, curvatureTensor_swap_last,
      D.curvatureTensor_swap_first x v u u v]
    ring
  have hh := hsec (a • u + b • v) (c • u + d • v) hp hq hpq
  unfold sectionalCurvature at hh
  change 0 < D.curvatureTensor x (a • u + b • v) (c • u + d • v)
    (a • u + b • v) (c • u + d • v) /
    (inner ℝ (a • u + b • v) (a • u + b • v) *
      inner ℝ (c • u + d • v) (c • u + d • v) -
      inner ℝ (a • u + b • v) (c • u + d • v) ^ 2) at hh
  rw [hp, hq, hpq, hnum] at hh
  norm_num only [one_mul, zero_pow, sub_zero, div_one] at hh
  exact pos_of_mul_pos_right hh (sq_nonneg _)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData.StrictlyPositiveSectionalCurvature

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}

theorem curvatureTensor_pos (hpos : D.StrictlyPositiveSectionalCurvature)
    (x : M) {u v : TangentSpace (𝓡 3) x} (hxy : LinearIndependent ℝ ![u, v]) :
    0 < D.curvatureTensor x u v u v :=
  D.curvatureTensor_diagonal_pos_of_orthonormal x (hpos x) hxy

end PoincareConjecture.LeviCivitaData.StrictlyPositiveSectionalCurvature
