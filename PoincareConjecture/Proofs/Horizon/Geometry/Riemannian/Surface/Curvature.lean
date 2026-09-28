import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {S : Type u} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

private lemma curvatureTensor_diagonal_swap (D : LeviCivitaData g) (x : S)
    (v w : TangentSpace (𝓡 2) x) :
    D.curvatureTensor x v w v w = D.curvatureTensor x w v w v := by
  rw [D.curvatureTensor_swap_first x v w v w,
    D.curvatureTensor_swap_last x w v v w, neg_neg]


lemma scalarCurvature_eq_sum_frame (D : LeviCivitaData g) (x : S)
    (b : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    D.scalarCurvature x = ∑ i, ∑ j,
      D.curvatureTensor x (b i) (b j) (b i) (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let c := g.orthonormalBasis x
  change (∑ i, ∑ j, D.curvatureTensor x (c i) (c j) (c i) (c j)) = _
  calc
    _ = ∑ j, ∑ i, D.curvatureTensor x (c i) (c j) (c i) (c j) :=
      Finset.sum_comm
    _ = ∑ j, ∑ i, D.curvatureTensor x (b i) (c j) (b i) (c j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact bilinear_sum_orthonormalBasis_eq
        (D.curvatureTensor_bilinear_first_third x (c j) (c j)) c b
    _ = ∑ i, ∑ j, D.curvatureTensor x (b i) (c j) (b i) (c j) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [curvatureTensor_diagonal_swap D x (b i)]
      exact bilinear_sum_orthonormalBasis_eq
        (D.curvatureTensor_bilinear_first_third x (b i) (b i)) c b


theorem scalarCurvature_eq_twice_curvatureTensor (D : LeviCivitaData g) (x : S)
    (b : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    D.scalarCurvature x = 2 * D.curvatureTensor x (b 0) (b 1) (b 0) (b 1) := by
  have hzero (v : TangentSpace (𝓡 2) x) : D.curvatureTensor x v v v v = 0 := by
    have h := D.curvatureTensor_swap_first x v v v v
    linarith
  rw [D.scalarCurvature_eq_sum_frame x b]
  simp only [Fin.sum_univ_two, hzero, zero_add, add_zero]
  rw [curvatureTensor_diagonal_swap D x (b 1) (b 0)]
  ring


theorem scalarCurvature_eq_twice_sectionalCurvature (D : LeviCivitaData g) (x : S)
    (b : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    D.scalarCurvature x = 2 * D.sectionalCurvature x (b 0) (b 1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hb (i j : Fin 2) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  simpa [sectionalCurvature, hb] using D.scalarCurvature_eq_twice_curvatureTensor x b

private lemma curvatureTensor_frame_expansion (D : LeviCivitaData g) (x : S)
    (v w : TangentSpace (𝓡 2) x) (a b c d e f h i : ℝ) :
    D.curvatureTensor x (a • v + b • w) (c • v + d • w)
      (e • v + f • w) (h • v + i • w) =
      (a * d - b * c) * (e * i - f * h) * D.curvatureTensor x v w v w := by
  have hfirst (v w z : TangentSpace (𝓡 2) x) : D.curvatureTensor x v v w z = 0 := by
    have h := D.curvatureTensor_swap_first x v v w z
    linarith
  have hlast (v w z : TangentSpace (𝓡 2) x) : D.curvatureTensor x v w z z = 0 := by
    have h := D.curvatureTensor_swap_last x v w z z
    linarith
  simp only [D.curvatureTensor_add_first, D.curvatureTensor_smul_first,
    D.curvatureTensor_add_second, D.curvatureTensor_smul_second,
    D.curvatureTensor_add_third, D.curvatureTensor_smul_third,
    D.curvatureTensor_add_last, D.curvatureTensor_smul_last, hfirst, hlast,
    mul_zero, zero_add, add_zero]
  rw [D.curvatureTensor_swap_first x w v v w,
    D.curvatureTensor_swap_last x v w w v,
    curvatureTensor_diagonal_swap D x w v]
  ring


theorem curvatureTensor_eq_half_scalarCurvature (D : LeviCivitaData g) (x : S)
    (u v w z : TangentSpace (𝓡 2) x) :
    D.curvatureTensor x u v w z = D.scalarCurvature x / 2 *
      (g.inner x u w * g.inner x v z - g.inner x u z * g.inner x v w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  let b : OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x) :=
    (g.orthonormalBasis x).reindex (finCongr hd)
  have hexp (v : TangentSpace (𝓡 2) x) :
      v = g.inner x (b 0) v • b 0 + g.inner x (b 1) v • b 1 := by
    change v = inner ℝ (b 0) v • b 0 + inner ℝ (b 1) v • b 1
    simpa only [Fin.sum_univ_two] using (b.sum_repr' v).symm
  have hinner (v w : TangentSpace (𝓡 2) x) :
      g.inner x v w = g.inner x (b 0) v * g.inner x (b 0) w +
        g.inner x (b 1) v * g.inner x (b 1) w := by
    change inner ℝ v w = inner ℝ (b 0) v * inner ℝ (b 0) w +
      inner ℝ (b 1) v * inner ℝ (b 1) w
    simpa only [Fin.sum_univ_two, real_inner_comm v (b 0), real_inner_comm v (b 1)]
      using (b.sum_inner_mul_inner v w).symm
  have hR := D.scalarCurvature_eq_twice_curvatureTensor x b
  calc
    D.curvatureTensor x u v w z =
        (g.inner x (b 0) u * g.inner x (b 1) v -
          g.inner x (b 1) u * g.inner x (b 0) v) *
        (g.inner x (b 0) w * g.inner x (b 1) z -
          g.inner x (b 1) w * g.inner x (b 0) z) *
        D.curvatureTensor x (b 0) (b 1) (b 0) (b 1) := by
      conv_lhs => rw [hexp u, hexp v, hexp w, hexp z]
      exact curvatureTensor_frame_expansion D x (b 0) (b 1) _ _ _ _ _ _ _ _
    _ = _ := by
      rw [hR, hinner u w, hinner v z, hinner u z, hinner v w]
      ring


theorem sectionalCurvature_eq_half_scalarCurvature (D : LeviCivitaData g) (x : S)
    (u v : TangentSpace (𝓡 2) x)
    (hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0) :
    D.sectionalCurvature x u v = D.scalarCurvature x / 2 := by
  rw [sectionalCurvature, D.curvatureTensor_eq_half_scalarCurvature x,
    g.symm x v u, ← pow_two]
  exact mul_div_cancel_right₀ _ hgram

end PoincareConjecture.LeviCivitaData
