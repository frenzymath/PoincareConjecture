import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bilinear









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  {g : RiemannianMetric n M}

private theorem curvatureTensor_eq_sectionalCurvature_mul_of_unit
    (D : LeviCivitaData g) (x : M) (v e : TangentSpace (𝓡 n) x)
    (he : g.inner x e e = 1) :
    D.curvatureTensor x v e v e = D.sectionalCurvature x v e *
      (g.inner x v v - (g.inner x v e) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_cases hzero : g.inner x v v - (g.inner x v e) ^ 2 = 0
  · have hv : v = (g.inner x v e) • e := by
      apply sub_eq_zero.mp
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      change inner ℝ (v - (inner ℝ v e) • e) (v - (inner ℝ v e) • e) = 0
      change inner ℝ e e = 1 at he
      change inner ℝ v v - (inner ℝ v e) ^ 2 = 0 at hzero
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        inner_smul_right, he]
      rw [real_inner_comm v e]
      nlinarith only [hzero]
    have hdiag : D.curvatureTensor x e e v e = 0 := by
      simp [curvatureTensor, curvature, curvatureOnFields]
    let B := D.curvatureTensor_bilinear_first_third x e e
    have hlin : D.curvatureTensor x v e v e =
        (g.inner x v e) * D.curvatureTensor x e e v e := by
      change B v v = (g.inner x v e) * B e v
      conv_lhs => arg 1; rw [hv]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hlin, hdiag, hzero]
    simp
  · unfold sectionalCurvature
    rw [he, mul_one]
    exact (div_mul_cancel₀ _ hzero).symm



theorem abs_ricci_quadratic_le_of_abs_sectionalCurvature_le
    (D : LeviCivitaData g) (x : M) (K : ℝ)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, |D.sectionalCurvature x u w| ≤ K)
    (v : TangentSpace (𝓡 n) x) :
    |D.ricci x v v| ≤ ((n : ℝ) - 1) * K * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i) : g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow]
  have hgram (i) : 0 ≤ g.inner x v v - (g.inner x v (b i)) ^ 2 := by
    have h := real_inner_mul_inner_self_le v (b i)
    change (g.inner x v (b i)) * (g.inner x v (b i)) ≤
      g.inner x v v * g.inner x (b i) (b i) at h
    rw [hb, mul_one] at h
    nlinarith
  have hterm (i) : |D.curvatureTensor x v (b i) v (b i)| ≤
      K * (g.inner x v v - (g.inner x v (b i)) ^ 2) := by
    rw [D.curvatureTensor_eq_sectionalCurvature_mul_of_unit x v (b i) (hb i),
      abs_mul, abs_of_nonneg (hgram i)]
    exact mul_le_mul_of_nonneg_right (hsec v (b i)) (hgram i)
  have hparseval : (∑ i, (g.inner x v (b i)) ^ 2) = g.inner x v v := by
    change (∑ i, (inner ℝ v (b i)) ^ 2) = inner ℝ v v
    rw [b.sum_sq_inner_left, real_inner_self_eq_norm_sq]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  calc
    |D.ricci x v v| = |∑ i, D.curvatureTensor x v (b i) v (b i)| := rfl
    _ ≤ ∑ i, |D.curvatureTensor x v (b i) v (b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, K * (g.inner x v v - (g.inner x v (b i)) ^ 2) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = ((n : ℝ) - 1) * K * g.inner x v v := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hparseval]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim,
        nsmul_eq_mul]
      ring



theorem ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le
    (D : LeviCivitaData g) (x : M) (K : ℝ)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, |D.sectionalCurvature x u w| ≤ K)
    (v : TangentSpace (𝓡 n) x) :
    -((n : ℝ) - 1) * K * g.inner x v v ≤ D.ricci x v v := by
  have h := (abs_le.mp (D.abs_ricci_quadratic_le_of_abs_sectionalCurvature_le
    x K hsec v)).1
  linarith



theorem ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound
    (D : LeviCivitaData g) (x : M) (K : ℝ)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, -K ≤ D.sectionalCurvature x u w)
    (v : TangentSpace (𝓡 n) x) :
    -(((n : ℝ) - 1) * K) * g.inner x v v ≤ D.ricci x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i) : g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow]
  have hgram (i) : 0 ≤ g.inner x v v - (g.inner x v (b i)) ^ 2 := by
    have h := real_inner_mul_inner_self_le v (b i)
    change (g.inner x v (b i)) * (g.inner x v (b i)) ≤
      g.inner x v v * g.inner x (b i) (b i) at h
    rw [hb, mul_one] at h
    nlinarith
  have hterm (i) : -K * (g.inner x v v - (g.inner x v (b i)) ^ 2) ≤
      D.curvatureTensor x v (b i) v (b i) := by
    rw [D.curvatureTensor_eq_sectionalCurvature_mul_of_unit x v (b i) (hb i)]
    exact mul_le_mul_of_nonneg_right (hsec v (b i)) (hgram i)
  have hparseval : (∑ i, (g.inner x v (b i)) ^ 2) = g.inner x v v := by
    change (∑ i, (inner ℝ v (b i)) ^ 2) = inner ℝ v v
    rw [b.sum_sq_inner_left, real_inner_self_eq_norm_sq]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  calc
    -(((n : ℝ) - 1) * K) * g.inner x v v =
        ∑ i, -K * (g.inner x v v - (g.inner x v (b i)) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hparseval]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim,
        nsmul_eq_mul]
      ring
    _ ≤ ∑ i, D.curvatureTensor x v (b i) v (b i) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = D.ricci x v v := rfl


theorem scalarCurvature_lower_bound_of_sectionalCurvature_lower_bound
    (D : LeviCivitaData g) (x : M) (K : ℝ)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, -K ≤ D.sectionalCurvature x u w) :
    -(n : ℝ) * ((n : ℝ) - 1) * K ≤ D.scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hb (i) : g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 := by
    change inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1
    rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).norm_eq_one, one_pow]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  have hterm (i) : -(((n : ℝ) - 1) * K) ≤
      D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i) := by
    simpa only [hb, mul_one] using
      D.ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound x K hsec
        (g.orthonormalBasis x i)
  calc
    -(n : ℝ) * ((n : ℝ) - 1) * K =
        ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          -(((n : ℝ) - 1) * K) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim,
        nsmul_eq_mul]
      ring
    _ ≤ D.scalarCurvature x := Finset.sum_le_sum fun i _ => hterm i

end PoincareConjecture.LeviCivitaData
