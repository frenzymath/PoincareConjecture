import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.Symmetry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

private theorem bilinear_self_eq_zero_of_nonneg_of_trace_eq_zero
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ v, 0 ≤ B v v) (htrace : (∑ i, B (b i) (b i)) = 0) (v : E) :
    B v v = 0 := by
  have hcoord (u w : E) : B u w =
      ∑ i, ∑ j, B (b i) (b j) * inner ℝ (b i) u * inner ℝ (b j) w := by
    conv_lhs => rw [← b.sum_repr' u, ← b.sum_repr' w]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hquad (w : ι → ℝ) :
      0 ≤ ∑ i, ∑ j, B (b i) (b j) * w i * w j := by
    let z := b.repr.symm (WithLp.toLp 2 w)
    have hz := hB z
    rw [hcoord] at hz
    have hrepr (i) : inner ℝ (b i) z = w i := by
      rw [← b.repr_apply_apply]
      exact congrFun (congrArg WithLp.ofLp (b.repr.apply_symm_apply (WithLp.toLp 2 w))) i
    simpa only [hrepr] using hz
  have h := Poincare.LinearAlgebra.quadratic_le_trace_mul_sum_sq
    (fun i j => B (b i) (b j)) hquad (fun i => inner ℝ (b i) v)
  rw [← hcoord, htrace, zero_mul] at h
  exact le_antisymm h (hB v)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem ricci_nonneg_of_nonnegative_curvatureOperator
    (D : LeviCivitaData g) (x : M) (hoperator : D.NonnegativeCurvatureOperator x)
    (v : TangentSpace (𝓡 n) x) : 0 ≤ D.ricci x v v := by
  unfold ricci
  exact Finset.sum_nonneg fun i _ =>
    D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x hoperator v _

theorem ricci_self_eq_zero_of_nonnegative_curvatureOperator_of_scalar_eq_zero
    [T2Space M]
    (D : LeviCivitaData g) (x : M) (hoperator : D.NonnegativeCurvatureOperator x)
    (hscalar : D.scalarCurvature x = 0) (v : TangentSpace (𝓡 n) x) :
    D.ricci x v v = 0 := by
  have hRic := D.ricci_nonneg_of_nonnegative_curvatureOperator x hoperator
  have hupper := D.ricci_le_scalarCurvature_mul_inner_of_nonneg x hRic v
  rw [hscalar, zero_mul] at hupper
  exact le_antisymm hupper (hRic v)

theorem curvatureTensor_self_eq_zero_of_nonnegative_curvatureOperator_of_scalar_eq_zero
    [T2Space M]
    (D : LeviCivitaData g) (x : M) (hoperator : D.NonnegativeCurvatureOperator x)
    (hscalar : D.scalarCurvature x = 0) (u v : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v u v = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply bilinear_self_eq_zero_of_nonneg_of_trace_eq_zero
    (g.orthonormalBasis x) (D.curvatureTensor_bilinear_first_third x v v)
  · intro w
    exact D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x hoperator w v
  · simp only [curvatureTensor_bilinear_first_third_apply]
    have hswap (w : TangentSpace (𝓡 n) x) :
        D.curvatureTensor x w v w v = D.curvatureTensor x v w v w := by
      rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]
    simp_rw [hswap]
    exact D.ricci_self_eq_zero_of_nonnegative_curvatureOperator_of_scalar_eq_zero
      x hoperator hscalar v

theorem curvatureTensor_eq_zero_of_nonnegative_curvatureOperator_of_scalar_eq_zero
    [T2Space M]
    (D : LeviCivitaData g) (x : M) (hoperator : D.NonnegativeCurvatureOperator x)
    (hscalar : D.scalarCurvature x = 0) (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = 0 := by
  have hself :=
    D.curvatureTensor_self_eq_zero_of_nonnegative_curvatureOperator_of_scalar_eq_zero
      x hoperator hscalar
  have hrad (a b c : TangentSpace (𝓡 n) x) : D.curvatureTensor x a b c b = 0 := by
    have hsym := D.inner_radial_curvature_symm x a b c
    rw [g.symm x a] at hsym
    change D.curvatureTensor x a b c b = D.curvatureTensor x c b a b at hsym
    have h := hself (a + c) b
    simp only [D.curvatureTensor_add_first, D.curvatureTensor_add_third] at h
    rw [hself a b, hself c b, ← hsym] at h
    linarith
  have hcross (a b c d : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a b d c + D.curvatureTensor x a c d b = 0 := by
    have h := hrad a (b + c) d
    simp only [D.curvatureTensor_add_second, D.curvatureTensor_add_last] at h
    rw [hrad a b d, hrad a c d] at h
    linarith
  have h := congrArg (fun y => g.inner x y w) (D.curvature_cyclic_eq_zero x u v z)
  simp only [map_add, add_apply, map_zero, zero_apply] at h
  change D.curvatureTensor x u v w z + D.curvatureTensor x v z w u +
    D.curvatureTensor x z u w v = 0 at h
  have h1 := hcross v u z w
  have h2 := hcross z v u w
  rw [D.curvatureTensor_swap_first x v u w z] at h1
  rw [D.curvatureTensor_swap_first x z v w u] at h2
  linarith

end PoincareConjecture.LeviCivitaData
