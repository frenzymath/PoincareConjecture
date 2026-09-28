import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds


set_option autoImplicit false
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}


theorem sectionalCurvature_lower_bound_of_orthonormal
    (D : LeviCivitaData g) (x : M) {κ : ℝ} (hκ : κ ≤ 0)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x,
      g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
      κ ≤ D.sectionalCurvature x u v)
    (u v : TangentSpace (𝓡 n) x) :
    κ ≤ D.sectionalCurvature x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_cases hxy : LinearIndependent ℝ ![u, v]
  · obtain ⟨a, b, c, d, hdet, hp, hq, hpq⟩ :=
      exists_orthonormal_changeBasis u v hxy
    let p := a • u + b • v
    let q := c • u + d • v
    have hnum : D.curvatureTensor x p q p q =
        (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := by
      simp only [p, q, curvatureTensor_add_first, curvatureTensor_add_second,
        curvatureTensor_add_third, curvatureTensor_add_last,
        curvatureTensor_smul_first, curvatureTensor_smul_second,
        curvatureTensor_smul_third, curvatureTensor_smul_last,
        curvatureTensor_zero_first, curvatureTensor_zero_last]
      rw [curvatureTensor_swap_first, curvatureTensor_swap_last,
        D.curvatureTensor_swap_first x v u u v]
      ring
    have hgram : g.inner x p p * g.inner x q q - (g.inner x p q) ^ 2 =
        (a * d - b * c) ^ 2 *
          (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
      change ((inner ℝ p p) * inner ℝ q q - (inner ℝ p q) ^ 2) =
        (a * d - b * c) ^ 2 *
          (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2)
      simp only [p, q, inner_add_left, inner_add_right,
        real_inner_smul_right, real_inner_comm]
      ring
    have hchange : D.sectionalCurvature x p q = D.sectionalCurvature x u v := by
      unfold sectionalCurvature
      rw [hnum, hgram]
      field_simp [hdet]
    rw [← hchange]
    exact hsec p q hp hq hpq
  · rw [linearIndependent_fin2] at hxy
    have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 0 := by
      by_cases hv : v = 0
      · simp [hv]
      · obtain ⟨a, ha⟩ : ∃ a : ℝ, a • v = u := by
          by_contra hn
          push Not at hn
          exact (hxy ⟨hv, hn⟩).elim
        rw [← ha]
        change inner ℝ (a • v) (a • v) * inner ℝ v v -
          (inner ℝ (a • v) v) ^ 2 = 0
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
    rw [D.sectionalCurvature_eq_zero_of_gramDet_eq_zero x u v hgram]
    exact hκ
end PoincareConjecture.LeviCivitaData
