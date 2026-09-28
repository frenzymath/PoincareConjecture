import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.NullPlane

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30

theorem curvatureEvolution_nonpos_on_finite_terminal_null_plane
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (hab : a < b) (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    (F.connection b).tensorLaplacian (F.connection b).riemannEvaluation x ![v, w, v, w] +
      (F.connection b).curvatureReaction x v w v w ≤ 0 := by
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hmin : IsMinOn (fun t => (F.connection t).curvatureTensor x v w v w)
      (Icc a b) b := by
    intro t ht
    change (F.connection b).curvatureTensor x v w v w ≤ _
    rw [hzero]
    exact (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t ht x) v w
  have hcone : a - b ∈ posTangentConeAt (Icc a b) b :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset hb ⟨le_rfl, hab.le⟩)
  have h := hmin.localize.hasFDerivWithinAt_nonneg
    (hC.curvature_evolution n M (Icc a b) F b hb x v w v w).hasFDerivWithinAt hcone
  change 0 ≤ (a - b) * (_ + _) at h
  nlinarith

theorem curvatureReaction_nonpos_on_finite_terminal_null_plane
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (hab : a < b) (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    (F.connection b).curvatureReaction x v w v w ≤ 0 := by
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hlap := (F.connection b).tensorLaplacian_nonneg_on_null_plane
    (hC.tensor_calculus n M (F.metric b) (F.connection b))
    (fun y u z => (F.connection b).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (hoperator b hb y) u z) x v w hzero
  have hevol := curvatureEvolution_nonpos_on_finite_terminal_null_plane
    hab hC F hoperator x v w hzero
  linarith

end PoincareConjecture.M30
