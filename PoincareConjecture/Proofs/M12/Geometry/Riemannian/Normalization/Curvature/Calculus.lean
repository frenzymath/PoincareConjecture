import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Tensorial
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Algebra
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.TraceRegularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.DerivativeRegularity










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem normalization_isSmoothCovariantTensor_riemannEvaluation
    (D : LeviCivitaData g) : IsSmoothCovariantTensor D.riemannEvaluation := by
  constructor
  · exact D.curvatureTensor_multilinear
  · intro U hU X hX
    exact D.riemannEvaluation_smooth hU X hX

private theorem normalization_isSmoothCovariantTensor_ricciEvaluation
    (D : LeviCivitaData g) : IsSmoothCovariantTensor D.ricciEvaluation := by
  let σ : Equiv.Perm (Fin 4) :=
    { toFun := fun i => ![2, 0, 3, 1] i
      invFun := fun i => ![1, 3, 0, 2] i
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  let T : CovariantTensorEvaluation n M 4 :=
    fun x v => D.riemannEvaluation x (v ∘ σ)
  have hR := normalization_isSmoothCovariantTensor_riemannEvaluation D
  have hT : IsSmoothCovariantTensor T := hR.perm σ
  have htrace := IsSmoothCovariantTensor.tensorTrace (g := g) hT
  convert htrace using 1
  funext x v
  simp [T, σ, RiemannianMetric.tensorTrace, riemannEvaluation,
    ricciEvaluation, ricci]
  apply Finset.sum_congr rfl
  intro i _
  rfl

private theorem normalization_curvature_cyclic_eq_zero
    (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w + D.curvature x v w u + D.curvature x w u v = 0 := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hX := contMDiffOn_extend_baseSet x u
  have hY := contMDiffOn_extend_baseSet x v
  have hZ := contMDiffOn_extend_baseSet x w
  have h := D.curvatureOnFields_bianchi e.open_baseSet X Y Z hX hY hZ
    (FiberBundle.mem_baseSet_trivializationAt' x)
  simpa [curvature, X, Y, Z] using h

private theorem normalization_curvatureTensor_cyclic
    (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z + D.curvatureTensor x v w u z +
      D.curvatureTensor x w u v z = 0 := by
  have h := congrArg (fun a => g.inner x a z)
    (normalization_curvature_cyclic_eq_zero D x u v w)
  simp only [map_add, add_apply, map_zero, zero_apply] at h
  change D.curvatureTensor x u v z w + D.curvatureTensor x v w z u +
    D.curvatureTensor x w u z v = 0 at h
  rw [D.curvatureTensor_swap_last x u v z w,
    D.curvatureTensor_swap_last x v w z u,
    D.curvatureTensor_swap_last x w u z v] at h
  linarith only [h]

private theorem normalization_curvatureTensor_pair_exchange
    (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = D.curvatureTensor x w z u v := by
  have h1 := normalization_curvatureTensor_cyclic D x u v w z
  have h2 := normalization_curvatureTensor_cyclic D x u v z w
  have h3 := normalization_curvatureTensor_cyclic D x w z u v
  have h4 := normalization_curvatureTensor_cyclic D x v w z u
  rw [D.curvatureTensor_swap_last x u v z w] at h2
  rw [D.curvatureTensor_swap_last x z u w v,
    D.curvatureTensor_swap_last x u w z v,
    D.curvatureTensor_swap_first x u w v z, neg_neg] at h3
  rw [D.curvatureTensor_swap_last x v w z u,
    D.curvatureTensor_swap_last x w z v u,
    D.curvatureTensor_swap_last x z v w u,
    D.curvatureTensor_swap_first x z v u w, neg_neg] at h4
  linarith only [h1, h2, h3, h4]

private theorem normalization_ricci_symm
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = D.ricci x v u := by
  unfold ricci
  apply Finset.sum_congr rfl
  intro i _
  exact normalization_curvatureTensor_pair_exchange D x u _ v _



theorem normalization_curvatureTensorCalculus (D : LeviCivitaData g) :
    D.CurvatureTensorCalculus := by
  refine ⟨normalization_isSmoothCovariantTensor_riemannEvaluation D,
    normalization_isSmoothCovariantTensor_ricciEvaluation D, ?_, ?_, ?_⟩
  · intro k T hT
    exact D.covariantTensorDerivative_isSmooth hT
  · intro x u v w z
    exact ⟨D.curvatureTensor_swap_last x u v w z,
      normalization_curvatureTensor_pair_exchange D x u v w z,
      normalization_curvatureTensor_cyclic D x u v w z,
      normalization_ricci_symm D x u v⟩
  · intro U hU X Y Z hX hY hZ x hx
    exact D.curvatureOnFields_eq_curvature hU X Y Z hX hY hZ hx

end PoincareConjecture.LeviCivitaData
