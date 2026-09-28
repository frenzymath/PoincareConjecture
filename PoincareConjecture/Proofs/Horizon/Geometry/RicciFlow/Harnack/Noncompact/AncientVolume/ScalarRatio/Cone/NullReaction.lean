import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.NullPlane

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureReaction_eq_zero_of_curvature_null_vector
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (hnull : ∀ a b : TangentSpace (𝓡 n) x, D.curvature x a b v = 0)
    (a b c : TangentSpace (𝓡 n) x) :
    D.curvatureReaction x v a b c = 0 := by
  have hlast (u w z : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x u w z v = 0 := by
    simp only [curvatureTensor, hnull, map_zero, zero_apply]
  have hfirst (u w z : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x v u w z = 0 := by
    rw [(hD.2.2.2.1 x v u w z).2.1,
      (hD.2.2.2.1 x w z v u).1, hlast, neg_zero]
  have hRic (u : TangentSpace (𝓡 n) x) : D.ricci x v u = 0 := by
    simp only [ricci, hfirst, Finset.sum_const_zero]
  simp only [curvatureReaction, curvatureB, hfirst, hRic, zero_mul,
    Finset.sum_const_zero, sub_zero, mul_zero, add_zero]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow

theorem tensorLaplacian_nonpos_on_terminal_curvature_null_vector
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hnull : ∀ a b : TangentSpace (𝓡 n) x, (F.connection 0).curvature x a b v = 0) :
    (F.connection 0).tensorLaplacian (F.connection 0).riemannEvaluation
      x ![v, w, v, w] ≤ 0 := by
  have hD := hC.tensor_calculus n M (F.metric 0) (F.connection 0)
  have hzero : (F.connection 0).curvatureTensor x v w v w = 0 := by
    rw [(hD.2.2.2.1 x v w v w).1]
    simp only [LeviCivitaData.curvatureTensor, hnull, map_zero, zero_apply, neg_zero]
  have h := F.curvatureEvolution_nonpos_on_terminal_null_plane hC hoperator x v w hzero
  simpa only [(F.connection 0).curvatureReaction_eq_zero_of_curvature_null_vector
    hD x v hnull w v w, add_zero] using h

end PoincareConjecture.RicciFlow
