import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Curvature.Tensorial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.DerivativeRegularity







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem curvatureTensor_cyclic_last (D : LeviCivitaData g)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v z w + D.curvatureTensor x v w z u +
      D.curvatureTensor x w u z v = 0 := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hX := contMDiffOn_extend_baseSet x u
  have hY := contMDiffOn_extend_baseSet x v
  have hZ := contMDiffOn_extend_baseSet x w
  have hx := FiberBundle.mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x
  have hb := D.curvatureOnFields_bianchi e.open_baseSet X Y Z hX hY hZ hx
  rw [D.curvatureOnFields_eq_curvature e.open_baseSet X Y Z hX hY hZ hx,
    D.curvatureOnFields_eq_curvature e.open_baseSet Y Z X hY hZ hX hx,
    D.curvatureOnFields_eq_curvature e.open_baseSet Z X Y hZ hX hY hx] at hb
  have hp := congrArg (fun a => g.inner x a z) hb
  simpa only [X, Y, Z, FiberBundle.extend_apply_self, map_add, add_apply,
    map_zero, zero_apply, curvatureTensor] using hp

theorem curvatureTensor_cyclic (D : LeviCivitaData g)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z + D.curvatureTensor x v w u z +
      D.curvatureTensor x w u v z = 0 := by
  have h := curvatureTensor_cyclic_last D x u v w z
  rw [D.curvatureTensor_swap_last x u v z w,
    D.curvatureTensor_swap_last x v w z u,
    D.curvatureTensor_swap_last x w u z v] at h
  linarith

theorem curvatureTensor_pair_swap (D : LeviCivitaData g)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = D.curvatureTensor x w z u v := by
  have h1 := D.curvatureTensor_cyclic x u v w z
  have h2 := D.curvatureTensor_cyclic x v w z u
  have h3 := D.curvatureTensor_cyclic x w z u v
  have h4 := D.curvatureTensor_cyclic x z u v w
  have s1 := D.curvatureTensor_swap_last x v w z u
  have s2 := D.curvatureTensor_swap_last x w z v u
  have s3 := D.curvatureTensor_swap_first x w u v z
  have s4 := D.curvatureTensor_swap_last x u w v z
  have s5 := D.curvatureTensor_swap_first x z v w u
  have s6 := D.curvatureTensor_swap_last x v z w u
  have s7 := D.curvatureTensor_swap_last x z u v w
  have s8 := D.curvatureTensor_swap_last x u v z w
  linarith

theorem ricci_symmetric (D : LeviCivitaData g)
    (x : M) (u v : TangentSpace (𝓡 n) x) : D.ricci x u v = D.ricci x v u := by
  unfold ricci
  exact Finset.sum_congr rfl fun i _ => D.curvatureTensor_pair_swap x u _ v _


theorem intrinsicCurvatureTensorCalculus (D : LeviCivitaData g) :
    D.CurvatureTensorCalculus := by
  refine ⟨D.riemannEvaluation_isSmooth_manifold, D.ricciEvaluation_isSmooth_manifold,
    fun _ _ h => D.covariantTensorDerivative_isSmooth h, ?_, ?_⟩
  · intro x u v w z
    exact ⟨D.curvatureTensor_swap_last x u v w z,
      D.curvatureTensor_pair_swap x u v w z, D.curvatureTensor_cyclic x u v w z,
      D.ricci_symmetric x u v⟩
  · intro U hU X Y Z hX hY hZ x hx
    exact D.curvatureOnFields_eq_curvature hU X Y Z hX hY hZ hx

end PoincareConjecture.LeviCivitaData
