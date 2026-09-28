import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma curvatureTensor_sum_frame (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v u v =
      ∑ i, ∑ j, ∑ k, ∑ l,
        D.curvatureTensor x (g.orthonormalBasis x i) (g.orthonormalBasis x j)
          (g.orthonormalBasis x k) (g.orthonormalBasis x l) *
          g.inner x (g.orthonormalBasis x i) u *
          g.inner x (g.orthonormalBasis x j) v *
          g.inner x (g.orthonormalBasis x k) u *
          g.inner x (g.orthonormalBasis x l) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hpair (p q y z : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x p y q z =
        ∑ i, ∑ k, D.curvatureTensor x (b i) y (b k) z *
          inner ℝ (b i) p * inner ℝ (b k) q := by
    rw [← D.curvatureTensor_bilinear_first_third_apply]
    conv_lhs => rw [← b.sum_repr' p, ← b.sum_repr' q]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    simp only [curvatureTensor_bilinear_first_third_apply]
    ring
  have hswap (p q y z : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x p y q z = D.curvatureTensor x y p z q := by
    rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]
  rw [hpair u u v v]
  simp_rw [hswap (b _) (b _) v v, hpair v v (b _) (b _)]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [← hswap (b i) (b k) (b j) (b l)]
  change _ = _ * inner ℝ (b i) u * inner ℝ (b j) v * inner ℝ (b k) u * inner ℝ (b l) v
  ring

theorem curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
    (D : LeviCivitaData g) (x : M) (hoperator : D.NonnegativeCurvatureOperator x)
    (u v : TangentSpace (𝓡 n) x) : 0 ≤ D.curvatureTensor x u v u v := by
  let b := g.orthonormalBasis x
  let U := fun i => g.inner x (b i) u
  let V := fun i => g.inner x (b i) v
  let A := fun i j => (U i * V j - V i * U j) / 2
  have hA : IsSkewCoefficient _ A := by
    intro i j
    dsimp only [A]
    ring
  have hop := hoperator A hA
  unfold curvatureOperatorQuadratic at hop
  let R := fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have heq := Poincare.RicciFlow.Harnack.curvature_contraction_half_wedge R
    (fun i j k l => D.curvatureTensor_swap_first x (b i) (b j) (b k) (b l))
    (fun i j k l => D.curvatureTensor_swap_last x (b i) (b j) (b k) (b l)) U V
  have hnonneg : 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * A i j * A k l := by
    change 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l at hop
    convert hop using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  dsimp only [A] at hnonneg
  rw [heq] at hnonneg
  rw [D.curvatureTensor_sum_frame x u v]
  exact hnonneg

theorem sectionalCurvature_nonneg_of_nonnegative_curvatureOperator
    (D : LeviCivitaData g) (x : M) (hoperator : D.NonnegativeCurvatureOperator x)
    (u v : TangentSpace (𝓡 n) x) : 0 ≤ D.sectionalCurvature x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply div_nonneg (D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x hoperator u v)
  change 0 ≤ inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2
  simpa only [pow_two] using sub_nonneg.mpr (real_inner_mul_inner_self_le u v)

end PoincareConjecture.LeviCivitaData
