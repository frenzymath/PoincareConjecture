import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalSectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u v

namespace PoincareConjecture.MetricSurgery

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureTensor_plane_swap (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x v w v w = D.curvatureTensor x w v w v := by
  rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]

theorem scalarCurvature_eq_sum_orthonormal (D : LeviCivitaData g) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type v} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x)),
      D.scalarCurvature x = ∑ i, ∑ j, D.curvatureTensor x (b i) (b j) (b i) (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro ι _ b
  let c := g.orthonormalBasis x
  have htrace (v : TangentSpace (𝓡 n) x) :
      (∑ i, D.curvatureTensor x (c i) v (c i) v) =
        ∑ i, D.curvatureTensor x (b i) v (b i) v :=
    bilinear_sum_orthonormalBasis_eq (D.curvatureTensor_bilinear_first_third x v v) c b
  change (∑ i, ∑ j, D.curvatureTensor x (c i) (c j) (c i) (c j)) = _
  calc
    _ = ∑ j, ∑ i, D.curvatureTensor x (b i) (c j) (b i) (c j) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => htrace (c j)
    _ = ∑ i, ∑ j, D.curvatureTensor x (b i) (c j) (b i) (c j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [curvatureTensor_plane_swap D x] using htrace (b i)

theorem sectionalCurvature_self (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 n) x) : D.sectionalCurvature x v v = 0 := by
  simp [LeviCivitaData.sectionalCurvature, pow_two]

theorem sectionalCurvature_smul_pair (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    D.sectionalCurvature x (a • v) (b • w) = D.sectionalCurvature x v w := by
  unfold LeviCivitaData.sectionalCurvature
  simp only [D.curvatureTensor_smul_first, D.curvatureTensor_smul_second,
    D.curvatureTensor_smul_third, D.curvatureTensor_smul_last,
    map_smul, smul_apply, smul_eq_mul]
  have hnum : a * (b * (a * (b * D.curvatureTensor x v w v w))) =
      (a ^ 2 * b ^ 2) * D.curvatureTensor x v w v w := by ring
  have hden : (a * (a * g.inner x v v)) * (b * (b * g.inner x w w)) -
      (b * (a * g.inner x v w)) ^ 2 =
        (a ^ 2 * b ^ 2) * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2) := by ring
  rw [hnum, hden]
  exact mul_div_mul_left _ _ (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb))

theorem scalarCurvature_eq_sum_sectional (D : LeviCivitaData g) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type v} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x)),
      D.scalarCurvature x = ∑ i, ∑ j, D.sectionalCurvature x (b i) (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro ι _ b
  rw [scalarCurvature_eq_sum_orthonormal D x b]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [sectionalCurvature_self]
    have h := D.curvatureTensor_swap_first x (b i) (b i) (b i) (b i)
    linarith
  · have hii : g.inner x (b i) (b i) = 1 := b.inner_eq_one i
    have hjj : g.inner x (b j) (b j) = 1 := b.inner_eq_one j
    have hijg : g.inner x (b i) (b j) = 0 := b.inner_eq_zero hij
    simp [LeviCivitaData.sectionalCurvature, hii, hjj, hijg]

end PoincareConjecture.MetricSurgery
