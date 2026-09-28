import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Sectional








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem curvatureTensor_diagonal_lower_bound_of_orthonormal
    (D : LeviCivitaData g) (x : M) {κ : ℝ}
    (hsec : ∀ u v : TangentSpace (𝓡 n) x,
      g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
      κ ≤ D.sectionalCurvature x u v)
    (u v : TangentSpace (𝓡 n) x) :
    κ * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
      D.curvatureTensor x u v u v := by
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
      change inner ℝ p p * inner ℝ q q - (inner ℝ p q) ^ 2 =
        (a * d - b * c) ^ 2 *
          (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2)
      simp only [p, q, inner_add_left, inner_add_right,
        real_inner_smul_right, real_inner_comm]
      ring
    have hgram_one : (a * d - b * c) ^ 2 *
        (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) = 1 := by
      rw [show g.inner x p p = 1 from hp,
        show g.inner x q q = 1 from hq,
        show g.inner x p q = 0 from hpq] at hgram
      simpa using hgram.symm
    have hbound := hsec p q hp hq hpq
    unfold sectionalCurvature at hbound
    rw [show g.inner x p p = 1 from hp,
      show g.inner x q q = 1 from hq,
      show g.inner x p q = 0 from hpq, hnum] at hbound
    norm_num only [one_mul, zero_pow, sub_zero, div_one] at hbound
    refine le_of_mul_le_mul_left ?_ (sq_pos_of_ne_zero hdet)
    calc
      (a * d - b * c) ^ 2 *
          (κ * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) =
          κ * ((a * d - b * c) ^ 2 *
            (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) := by ring
      _ = κ := by rw [hgram_one, mul_one]
      _ ≤ (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := hbound
  · rw [linearIndependent_fin2] at hxy
    by_cases hv : v = 0
    · have hnum : D.curvatureTensor x u 0 u 0 = 0 := by
        have hz := D.curvatureTensor_smul_second x 0 u 0 u 0
        simpa only [zero_smul, zero_mul] using hz
      simp [hv, hnum]
    · obtain ⟨a, ha⟩ : ∃ a : ℝ, a • v = u := by
        by_contra hn
        push Not at hn
        exact (hxy ⟨hv, hn⟩).elim
      have hnum : D.curvatureTensor x u v u v = 0 := by
        rw [← ha, curvatureTensor_smul_first, curvatureTensor_zero_first]
        simp
      have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 0 := by
        rw [← ha]
        change inner ℝ (a • v) (a • v) * inner ℝ v v -
          (inner ℝ (a • v) v) ^ 2 = 0
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
      rw [hnum, hgram, mul_zero]

end PoincareConjecture.LeviCivitaData
